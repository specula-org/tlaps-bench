#!/usr/bin/env python3
"""
Check a single TLAPS benchmark proof for correctness and cheating.

Designed for AI agents to get quick feedback during proof writing.

Usage:
    python3 check_proof.py benchmark/Euclid/GCD_GCD3.tla \\
        [--level {1,2}] [--tlapm PATH] [--tlapm-lib PATH] [--timeout SECS]

Levels:
    1 (default) — proof completion. The preamble (above PROOF OBVIOUS) must be
                  byte-identical to the baseline.
    2          — proof from scratch. The agent may add new LEMMAs above the
                  target theorem; preamble integrity is not enforced. Other
                  cheating checks (PROOF OMITTED, axiom injection, bare QED,
                  dependency tampering) still apply.

Output:
    - Raw tlapm output (preserved verbatim)
    - Cheating check (compares against main branch where applicable)
    - Binary verdict: PASS / FAIL. A cheat is not a separate verdict — it is just
      a FAIL; the failing gate is shown in the output and on a GATES-FAILED line.

Exit codes:
    0 = PASS
    1 = FAIL (proof doesn't verify, or a soundness gate failed)
    3 = ERROR (could not run check)
"""

import argparse
import contextlib
import glob
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile

from common.cheating_detection import (
    detect_dependency_modification,
    detect_empty_proof,
    detect_extra_axioms,
    detect_missing_proof,
    detect_missing_proofs_summary,
    detect_preamble_modification,
    detect_proof_omitted,
    detect_zero_total_obligations,
    strip_comments,
)
from common.container import ContainerConfig, ContainerRunner, ensure_image


def _descendant_pids(root_pid):
    """Snapshot every descendant of `root_pid` by walking /proc PPid chains.

    Returned leaves-first so the deepest survivors die before any parent has
    a chance to fork a replacement. Robust against descendants that have
    escaped `root_pid`'s process group or session — only the PPid chain
    matters, which holds as long as we snapshot before any kills land.
    """
    parents = {}
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/status") as f:
                for line in f:
                    if line.startswith("PPid:"):
                        parents[int(entry)] = int(line.split()[1])
                        break
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    children = {}
    for child, parent in parents.items():
        children.setdefault(parent, []).append(child)
    order = []
    stack = list(children.get(root_pid, []))
    while stack:
        pid = stack.pop()
        order.append(pid)
        stack.extend(children.get(pid, []))
    return list(reversed(order))


def run_killgroup(cmd, timeout, cwd):
    """Run `cmd` with a wall-clock `timeout`, killing tlapm AND every backend
    it spawned on timeout. Returns (stdout, stderr, returncode); re-raises
    subprocess.TimeoutExpired after cleanup.

    tlapm spawns its backend solvers (z3, cvc4, zenon, isabelle, ...) as
    separate processes. subprocess.run's timeout would kill only tlapm,
    orphaning the solvers — they keep running, steal CPU and tens of GB of
    RAM, and the accumulated tax stalls every later verification. We defend
    in two layers: `start_new_session=True` puts tlapm in its own process
    group and, on timeout, `killpg` SIGKILLs every member. That suffices for
    z3/cvc4/zenon (they inherit tlapm's pgid). It does NOT catch Isabelle,
    whose `bash_process` wrapper `setsid`'s into its own session — and any
    z3 spawned via the Isabelle backend rides along into that escape. So we
    additionally snapshot tlapm's PPid-chain descendants *before* killing
    (chain only holds while parents are alive) and SIGKILL each one,
    leaves-first. Covers Isabelle's polyml, isabelle.Isabelle_Tool, the
    `bash_process` wrapper, and any z3 they hold.
    """
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=cwd,
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(timeout=timeout)
        return out, err, proc.returncode
    except subprocess.TimeoutExpired:
        escapees = _descendant_pids(proc.pid)
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        for pid in escapees:
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(pid, signal.SIGKILL)
        with contextlib.suppress(Exception):
            proc.communicate(timeout=10)
        raise


def find_tlapm():
    """Find tlapm binary."""
    candidates = [
        "/opt/tlapm/bin/tlapm",
        os.path.expanduser("~/.tlapm/bin/tlapm"),
        "/tmp/tlapm/bin/tlapm",
        shutil.which("tlapm"),
    ]
    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            return candidate
    return None


def find_tlapm_lib(tlapm_path):
    """Derive lib path from tlapm binary path.

    tlapm 1.6 puts stdlib at lib/tlapm/stdlib; tlapm 1.5 used lib/tlaps.
    The 1.6 sub is checked first because lib/tlapm exists in 1.6 too but
    does NOT directly contain the .tla files.
    """
    base = os.path.dirname(os.path.dirname(tlapm_path))
    for sub in ["lib/tlapm/stdlib", "lib/tlaps", "lib/tlapm", "lib"]:
        path = os.path.join(base, sub)
        if os.path.isdir(path):
            return path
    return None


def find_community_lib(filepath):
    """Find vendored CommunityModules (lib/community/), searching the file's
    git repo root then ancestor dirs. Returns the path or None.

    NOTE: this script is compiled to a standalone binary (see Makefile) and runs
    inside the agent's workspace, so unlike validate.py it can't rely on a
    repo-relative PROJECT_ROOT — it must discover lib/community/ at runtime."""
    candidates = []
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(filepath) or ".",
    ).stdout.strip()
    if repo_root:
        candidates.append(os.path.join(repo_root, "lib", "community"))
    d = os.path.dirname(os.path.abspath(filepath))
    for _ in range(6):  # walk up a few levels as a fallback
        candidates.append(os.path.join(d, "lib", "community"))
        d = os.path.dirname(d)
    for c in candidates:
        if os.path.isdir(c):
            return c
    return None


def get_main_version(filepath):
    """Get the file content from the main/master branch."""
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, cwd=os.path.dirname(filepath) or "."
    ).stdout.strip()

    if not repo_root:
        return None

    rel_path = os.path.relpath(filepath, repo_root)

    for branch in ["main", "master"]:
        result = subprocess.run(["git", "show", f"{branch}:{rel_path}"], capture_output=True, text=True, cwd=repo_root)
        if result.returncode == 0:
            return result.stdout

    return None


def find_proof_obvious_line(lines):
    """Find the line number (0-indexed) of 'PROOF OBVIOUS' in the file."""
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "PROOF OBVIOUS":
            return i
    return None


def check_cheating(filepath, level: int = 1):
    """Check for cheating by comparing against main branch.

    Args:
        level: 1 = strict preamble + proof-section checks;
               2 = preamble may grow (the agent can add lemmas), so the
                   preamble-integrity check is skipped and PROOF OMITTED is
                   scanned across the whole current file.

    Returns list of (line_number_1indexed, description) issues.
    """
    issues = []

    # Get main branch version
    main_content = get_main_version(filepath)
    if main_content is None:
        issues.append((0, "WARNING: Could not retrieve main branch version for comparison"))
        return issues

    main_lines = main_content.split("\n")
    with open(filepath) as f:
        current_content = f.read()
    current_lines = current_content.split("\n")

    # Find PROOF OBVIOUS in main version - this is the boundary
    po_line = find_proof_obvious_line(main_lines)
    if po_line is None:
        issues.append((0, "WARNING: No PROOF OBVIOUS found in main branch version"))
        return issues

    if level == 1 and len(current_lines) < po_line:
        issues.append(
            (len(current_lines), f"File truncated: preamble had {po_line} lines, file has {len(current_lines)}")
        )
        return issues

    # 1. Preamble modification — L1 only.
    # L2 permits new declarations above the target theorem, so a byte-for-byte
    # preamble check would reject legitimate proofs.
    if level == 1:
        for ci in detect_preamble_modification(main_lines, current_lines, po_line):
            issues.append((ci.line or 0, ci.description))

    # 2. PROOF OMITTED / bare OMITTED.
    # L1: only the proof section can plausibly contain it (and must not).
    # L2: scan the whole current file — the agent may add proofs anywhere.
    if level == 1:
        proof_section = "\n".join(current_lines[po_line:])
        for ci in detect_proof_omitted(proof_section):
            issues.append((po_line + (ci.line or 0), ci.description))
    else:
        for ci in detect_proof_omitted(current_content):
            issues.append((ci.line or 0, ci.description))

    # 3. Extra AXIOM/ASSUME (shared module)
    for ci in detect_extra_axioms(main_content, current_content):
        issues.append((0, ci.description))

    # 4. Dependency file modification (shared module)
    bench_dir = os.path.dirname(filepath)
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, cwd=bench_dir or "."
    ).stdout.strip()

    if repo_root:
        dep_files = {}
        for dep_file in glob.glob(os.path.join(bench_dir, "*.tla")):
            if os.path.abspath(dep_file) == os.path.abspath(filepath):
                continue
            dep_basename = os.path.basename(dep_file)
            dep_rel = os.path.relpath(dep_file, repo_root)
            dep_main = None
            for branch in ["main", "master"]:
                r = subprocess.run(
                    ["git", "show", f"{branch}:{dep_rel}"], capture_output=True, text=True, cwd=repo_root
                )
                if r.returncode == 0:
                    dep_main = r.stdout
                    break
            if dep_main is None:
                continue
            with open(dep_file) as f:
                dep_current = f.read()
            dep_files[dep_basename] = (dep_main, dep_current)

        for ci in detect_dependency_modification(dep_files):
            issues.append((0, ci.description))

    return issues


def _git_root(path):
    r = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(os.path.abspath(path)) or ".",
    )
    return r.stdout.strip() if r.returncode == 0 else None


def _git_root_commit(repo_root):
    """The earliest (root) commit — the runner seeds it with the pristine
    benchmark, so it is a tamper-resistant baseline even if the agent commits."""
    r = subprocess.run(["git", "rev-list", "--max-parents=0", "HEAD"], capture_output=True, text=True, cwd=repo_root)
    if r.returncode != 0:
        return None
    commits = r.stdout.split()
    return commits[-1] if commits else None


def _reconstruct_from_git(filepath, target_name):
    """Reconstruct the pristine benchmark from the git root commit.

    Each agent workspace is seeded with one commit holding the original
    benchmark files. We materialize two temp dirs the tlacheck engine consumes:
      benchmark_dir — git-root versions of every .tla beside the target (the
                      authoritative provenance / GIVEN modules).
      solution_dir  — the agent's CURRENT .tla files, plus benchmark.tla set to
                      the git-root version of the target (the baseline).
    Returns (solution_dir, benchmark_dir, [tmpdirs]) or (None, None, []).
    """
    repo_root = _git_root(filepath)
    if not repo_root:
        return None, None, []
    root_commit = _git_root_commit(repo_root)
    if not root_commit:
        return None, None, []
    bench_dir = os.path.dirname(os.path.abspath(filepath))
    rel_dir = os.path.relpath(bench_dir, repo_root)
    tree = "" if rel_dir == "." else rel_dir
    spec = f"{root_commit}:{tree}" if tree else f"{root_commit}:"
    ls = subprocess.run(["git", "ls-tree", "--name-only", spec], capture_output=True, text=True, cwd=repo_root)
    if ls.returncode != 0:
        return None, None, []
    orig_tlas = [n for n in ls.stdout.split("\n") if n.endswith(".tla")]
    if not orig_tlas:
        return None, None, []

    sol_dir = tempfile.mkdtemp(prefix="tlck_sol_")
    bench_canon = tempfile.mkdtemp(prefix="tlck_bench_")
    cleanup = [sol_dir, bench_canon]

    for name in orig_tlas:
        path_in_tree = f"{tree}/{name}" if tree else name
        show = subprocess.run(
            ["git", "show", f"{root_commit}:{path_in_tree}"], capture_output=True, text=True, cwd=repo_root
        )
        if show.returncode == 0:
            with open(os.path.join(bench_canon, name), "w") as f:
                f.write(show.stdout)

    for dep in glob.glob(os.path.join(bench_dir, "*.tla")):
        shutil.copy2(dep, os.path.join(sol_dir, os.path.basename(dep)))
    orig_target = os.path.join(bench_canon, target_name + ".tla")
    if os.path.exists(orig_target):
        shutil.copy2(orig_target, os.path.join(sol_dir, "benchmark.tla"))

    return sol_dir, bench_canon, cleanup


def run_tlacheck_engine(filepath, target_name, summary_output, tlapm_passed, benchmark_dir=None):
    """Run the compiled-in SANY + incomplete-proof cheat engine.

    Folds CHEATING and INCOMPLETE findings into one list — any of them must fail
    the run. Returns ``(issue_strings, reason, result)`` where ``result`` is the
    tlacheck ``Result`` (or ``None`` on any internal error, so the engine never
    spuriously fails an otherwise-valid proof — ``result`` also feeds the shadow
    gate-framework verdict). ``benchmark_dir`` (when the runner
    supplies the canonical read-only module dir) is the tamper-proof provenance
    oracle; otherwise we reconstruct it from the git root commit.
    """
    try:
        from tlacheck.context import build_context
        from tlacheck.engine import evaluate
        from tlacore.tlapm.summary import parse_summary
    except Exception as e:
        return [], f"tlacheck import failed: {e}", None

    cleanup = []
    try:
        sol_dir, git_bench, cleanup = _reconstruct_from_git(filepath, target_name)
        bench = benchmark_dir or git_bench
        if sol_dir is None:
            if benchmark_dir is None:
                return [], "no git baseline available", None
            sol_dir = os.path.dirname(os.path.abspath(filepath))
        summary = parse_summary(summary_output) if summary_output else None
        ctx = build_context(
            sol_dir,
            target_name,
            benchmark_dir=bench,
            summary=summary,
            tlapm_passed=tlapm_passed,
            tlapm_fallback=True,
            compute_summary=(summary is None),
        )
        res = evaluate(ctx)
    except Exception as e:
        return [], f"tlacheck error: {e}", None
    finally:
        for d in cleanup:
            shutil.rmtree(d, ignore_errors=True)

    return ([str(i) for i in res.cheating_issues] + [str(i) for i in res.incomplete_issues]), "", res


# Machine-readable marker the runner greps for to set the structured
# `sany_valid` bit. Printed in the VERDICT section on a SANY parse failure.
SANY_INVALID_MARKER = "[SANY-INVALID]"


def check_sany_valid(filepath):
    """Whether the solution parses under standalone tla2sany — the canonical TLA+
    parser, which is stricter than tlapm's own (it rejects e.g. an operator
    parameter that shadows a state VARIABLE). Returns ``(status, detail)``:

      "valid"       — SANY parsed the module.
      "invalid"     — SANY reported a real parse/semantic error → hard FAIL.
      "unavailable" — SANY could not be run (run.sh / Java / tla2tools.jar
                      missing, or a timeout). Fail-open: we do NOT FAIL a proof
                      just because the SANY tooling is absent.

    Needs the Java SANY dumper reachable: the runner sets ``SANY_RUN_SH`` to
    ``src/dataset/sany-dump/run.sh`` for both the agent and the grader so the
    frozen ``check_proof_bin`` (which bundles the Python wrapper but not run.sh)
    can shell out to it.
    """
    try:
        from tlacore.sany.dump import SanyError, dump_normalized
    except Exception as e:
        return "unavailable", f"tlacore import failed: {e}"
    dep_dir = os.path.dirname(os.path.abspath(filepath))
    try:
        dump_normalized(filepath, dep_dir=dep_dir, timeout=120)
        return "valid", ""
    except SanyError as e:
        msg = str(e).replace("\n", " ")
        # A genuine rejection carries SANY's own diagnostics; a bare "produced no
        # dump" without them is an infrastructure failure (run.sh / Java missing),
        # not an invalid spec — treat that as unavailable, not invalid.
        low = msg.lower()
        if any(k in low for k in ("parse error", "errorlevel", "*** errors", "unknown operator", "multiply-defined")):
            return "invalid", msg
        return "unavailable", msg
    except Exception as e:
        return "unavailable", f"{type(e).__name__}: {e}"


def parse_strict_status(tlapm_exit, tlapm_output):
    """Interpret a ``tlapm --strict`` run. Returns ``(complete, n_missing, obligation_failed)``.

    ``--strict`` reports incompleteness MODULE-WIDE as "N missing, M omitted".
    Only MISSING steps (no proof at all — a bare QED, an unproven helper lemma,
    an unfinished target) are an agent gap. OMITTED steps are the benchmark's
    GIVEN admitted lemmas (L1 preceding ``PROOF OMITTED``) and must NOT by
    themselves fail a valid solution — agent-ADDED omitted is caught separately
    by the proof-omitted check.

    So a run is ``complete`` (target genuinely proved) iff every obligation was
    discharged and zero steps are missing — i.e. exit 0 (fully clean) or exit 11
    whose only gaps are omitted given lemmas. exit 10 / failed obligations /
    timeout (negative exit) are never complete.
    """
    m_missing = re.search(r"Proof incomplete in module .*?:\s*(\d+) missing", tlapm_output)
    n_missing = int(m_missing.group(1)) if m_missing else 0
    obligation_failed = "obligations failed" in tlapm_output or tlapm_exit == 10
    complete = tlapm_exit in (0, 11) and n_missing == 0 and not obligation_failed
    return complete, n_missing, obligation_failed


def _run_in_container(filepath, args):
    """Run check_proof_bin inside Docker container."""
    ensure_image(force=getattr(args, "force_build", False))
    runner = ContainerRunner()

    # Mount repo root so git cheating checks (main branch comparison) work
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(filepath) or ".",
    ).stdout.strip()

    result_dir = tempfile.mkdtemp(prefix="tlaps_check_docker_")

    if repo_root:
        rel_path = os.path.relpath(filepath, repo_root)
        container_file = f"/workspace/{rel_path}"
        workspace = repo_root
    else:
        container_file = f"/workspace/{os.path.basename(filepath)}"
        workspace = os.path.dirname(filepath)

    cmd = ["/usr/local/bin/check_proof_bin", container_file]
    cmd += ["--no-container"]
    cmd += ["--level", str(args.level)]
    cmd += ["--timeout", str(args.timeout)]
    cmd += ["--output", "/results/check.result"]
    if args.benchmark_dir:
        cmd += ["--benchmark-dir", os.path.dirname(container_file)]
    if args.sany_only:
        cmd += ["--sany-only"]

    config = ContainerConfig(workspace=workspace, result_dir=result_dir)
    config.env["GIT_CONFIG_COUNT"] = "1"
    config.env["GIT_CONFIG_KEY_0"] = "safe.directory"
    config.env["GIT_CONFIG_VALUE_0"] = "/workspace"
    try:
        exit_code, stdout, stderr = runner.run_with_output(config, cmd, timeout=args.timeout + 60)
        # Print output, filtering container-internal paths
        if stdout:
            for line in stdout.splitlines():
                if line.startswith("Result written to: /results/"):
                    continue
                print(line)
        if stderr:
            print(stderr, end="", file=sys.stderr)

        # Copy result file to expected output location
        container_result = os.path.join(result_dir, "check.result")
        output_path = args.output or (os.path.splitext(filepath)[0] + ".result")
        if os.path.isfile(container_result):
            shutil.copy2(container_result, output_path)
            print(f"\nResult written to: {output_path}")

        sys.exit(exit_code)
    finally:
        shutil.rmtree(result_dir, ignore_errors=True)


def main():
    parser = argparse.ArgumentParser(description="Check a single TLAPS benchmark proof")
    parser.add_argument("file", help="Path to the benchmark .tla file")
    parser.add_argument(
        "--level", type=int, default=1, choices=[1, 2], help="Benchmark level — controls cheating rules (default: 1)"
    )
    parser.add_argument("--tlapm", default=None, help="Path to tlapm binary")
    parser.add_argument("--tlapm-lib", default=None, help="Path to tlapm lib directory")
    parser.add_argument("--timeout", type=int, default=600, help="Timeout in seconds")
    parser.add_argument("--output", "-o", default=None, help="Write results to this file (default: <input>.result)")
    parser.add_argument(
        "--benchmark-dir",
        default=None,
        help="Canonical benchmark/<level>/<module>/ dir (provenance oracle; defaults to git-root reconstruction)",
    )
    parser.add_argument(
        "--sany-only",
        action="store_true",
        help="Fast SANY-validity check only: parse the file with standalone "
        "tla2sany and exit (0 valid, 1 invalid) WITHOUT running tlapm. For quick "
        "syntax feedback while writing a proof — the full check applies the same gate.",
    )
    # Container vs. host. Default is auto: use the local toolchain when a tlapm
    # is installed, else fall back to Docker. These two flags force either side.
    container_group = parser.add_mutually_exclusive_group()
    container_group.add_argument(
        "--no-container",
        action="store_true",
        help="Force running tlapm on the host, never Docker (requires a local tlapm installation)",
    )
    container_group.add_argument(
        "--container",
        action="store_true",
        help="Force running inside Docker even when a local tlapm is installed",
    )
    parser.add_argument(
        "--force-build",
        action="store_true",
        help="Rebuild Docker image before running",
    )
    args = parser.parse_args()

    filepath = os.path.abspath(args.file)
    if not os.path.isfile(filepath):
        print(f"ERROR: File not found: {filepath}")
        sys.exit(3)

    # Container vs. local: prefer the local toolchain when it is there, so a
    # native setup (and the integration tests, and a hand-run) "just works"
    # without flags; fall back to Docker only when no local tlapm is installed.
    # Already inside a container (TLAPS_IN_CONTAINER, baked into the image) → always
    # local, never nest. --no-container forces local; --container forces Docker.
    in_container = bool(os.environ.get("TLAPS_IN_CONTAINER"))
    if args.container or (not args.no_container and not in_container and find_tlapm() is None):
        _run_in_container(filepath, args)

    # Fast path: --sany-only skips tlapm and just reports whether the solution
    # parses under standalone tla2sany (seconds, vs a full proof run). Same gate
    # the full check applies, so the agent can iterate on syntax quickly.
    if args.sany_only:
        status, detail = check_sany_valid(filepath)
        if status == "valid":
            print("SANY OK — parses under standalone tla2sany")
            sys.exit(0)
        if status == "invalid":
            print(f"FAIL {SANY_INVALID_MARKER} — {detail[:300]}")
            sys.exit(1)
        print(f"WARNING: SANY check unavailable ({detail[:200]}) — could not run; not treated as invalid")
        sys.exit(0)

    # Set up output: write to file and stdout
    output_path = args.output
    if output_path is None:
        output_path = os.path.splitext(filepath)[0] + ".result"

    # Collect all output lines, print at end and write to file
    output_lines = []

    def emit(line=""):
        output_lines.append(line)
        print(line)

    def write_result_and_exit(code):
        with open(output_path, "w") as f:
            f.write("\n".join(output_lines) + "\n")
        sys.exit(code)

    # Find tlapm
    tlapm_path = args.tlapm or find_tlapm()
    if not tlapm_path:
        emit("ERROR: tlapm not found. Use --tlapm to specify path.")
        write_result_and_exit(3)

    tlapm_lib = args.tlapm_lib or find_tlapm_lib(tlapm_path)
    if not tlapm_lib:
        emit("ERROR: tlapm lib not found. Use --tlapm-lib to specify path.")
        write_result_and_exit(3)

    emit(f"Checking: {os.path.relpath(filepath)}")
    emit(f"tlapm: {tlapm_path}")
    emit()

    # --- Step 1: Run tlapm ---
    emit("=" * 60)
    emit("TLAPM OUTPUT")
    emit("=" * 60)

    tmp_dir = tempfile.mkdtemp(prefix="tlaps_check_")
    try:
        basename = os.path.basename(filepath)
        tmp_file = os.path.join(tmp_dir, basename)
        shutil.copy2(filepath, tmp_file)

        # Copy dependency files from the same directory
        bench_dir = os.path.dirname(filepath)
        for dep_file in glob.glob(os.path.join(bench_dir, "*.tla")):
            dep_basename = os.path.basename(dep_file)
            if dep_basename != basename:
                shutil.copy2(dep_file, os.path.join(tmp_dir, dep_basename))

        # --strict makes tlapm exit non-zero on an *incomplete* proof — a step
        # with no proof (missing / OMITTED / bare QED) generates no obligation,
        # so default tlapm reports "All N obligations proved" and exits 0 even
        # though the proof is unfinished (tlaplus/tlapm#271). Exit codes: 10
        # failed obligation, 11 incomplete proof, 12 empty target. This is the
        # authoritative replacement for our hand-rolled incomplete-proof heuristics.
        cmd = [tlapm_path, "--strict", "-I", tlapm_lib]
        community_lib = find_community_lib(filepath)
        if community_lib:
            cmd += ["-I", community_lib]
        cmd.append(tmp_file)
        try:
            out, err, rc = run_killgroup(cmd, args.timeout, tmp_dir)
            tlapm_output = out + err
            tlapm_exit = rc
        except subprocess.TimeoutExpired:
            tlapm_output = f"TIMEOUT after {args.timeout}s"
            tlapm_exit = -1
        except Exception as e:
            tlapm_output = f"ERROR: {e}"
            tlapm_exit = -2

        for line in tlapm_output.split("\n"):
            emit(line)
        # Interpret --strict: a valid solution is "complete" (all obligations
        # discharged, no MISSING step); the benchmark's GIVEN omitted lemmas do
        # not count against it. See parse_strict_status for the full rationale.
        tlapm_passed, n_missing, obligation_failed = parse_strict_status(tlapm_exit, tlapm_output)

        # Run --summary to detect missing proofs (e.g. bare QED)
        summary_output = ""
        if tlapm_passed:
            summary_cmd = [tlapm_path, "-I", tlapm_lib]
            if community_lib:
                summary_cmd += ["-I", community_lib]
            summary_cmd += ["--summary", tmp_file]
            try:
                out, err, _ = run_killgroup(summary_cmd, 30, tmp_dir)
                summary_output = out + err
            except Exception:
                pass
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)

    # --- Step 2: Cheating check ---
    emit()
    emit("=" * 60)
    emit("CHEATING CHECK")
    emit("=" * 60)

    cheating_issues = check_cheating(filepath, level=args.level)
    real_issues = [i for i in cheating_issues if not i[1].startswith("WARNING:")]
    warnings = [i for i in cheating_issues if i[1].startswith("WARNING:")]

    # Check for empty PROOF blocks and 0-obligation (independent of git comparison)
    if tlapm_passed:
        with open(filepath) as f:
            cur_lines = f.read().split("\n")

        if args.level == 1:
            # L1: PROOF OBVIOUS in main is the boundary; slice current at the
            # same index because the preamble is required to be unchanged.
            main_content = get_main_version(filepath)
            if main_content:
                main_lines = main_content.split("\n")
                po_line = find_proof_obvious_line(main_lines)
                if po_line is not None:
                    proof_section = "\n".join(cur_lines[po_line:])
                    clean = strip_comments(proof_section)
                    for ci in detect_empty_proof(clean):
                        real_issues.append((po_line + (ci.line or 0), ci.description))
                    for ci in detect_zero_total_obligations(tlapm_output):
                        real_issues.append((0, ci.description))
                    for ci in detect_missing_proof(main_lines, cur_lines, po_line):
                        real_issues.append((ci.line or 0, ci.description))
        else:
            # L2: the agent may grow the preamble (new lemmas above target),
            # so there's no stable boundary. Scan the whole file; the bare-QED
            # check via --summary below catches what detect_missing_proof did.
            clean = strip_comments("\n".join(cur_lines))
            for ci in detect_empty_proof(clean):
                real_issues.append((ci.line or 0, ci.description))
            for ci in detect_zero_total_obligations(tlapm_output):
                real_issues.append((0, ci.description))

        # --summary missing-proofs check is shared (target theorem is still
        # the last THEOREM/LEMMA in the file for both levels).
        if summary_output:
            target_line = None
            for li, line in enumerate(cur_lines):
                if re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", line.strip()):
                    target_line = li + 1  # 1-indexed
            for ci in detect_missing_proofs_summary(summary_output, target_line):
                real_issues.append((0, ci.description))

    # --- SANY semantic engine (compiled-in): extra axioms, weakened/modified
    # statements, dependency tampering, smuggled modules, AND bare-QED holes in
    # ANY helper lemma (not just the target). Runs on every check so the agent
    # gets the same verdict the grader does. Any finding fails the run.
    target_name = os.path.splitext(os.path.basename(filepath))[0]
    engine_issues, engine_reason, engine_result = run_tlacheck_engine(
        filepath, target_name, summary_output, tlapm_passed, benchmark_dir=args.benchmark_dir
    )
    if engine_reason:
        warnings.append((0, f"semantic engine skipped ({engine_reason})"))
    for desc in engine_issues:
        real_issues.append((0, desc))

    # SANY validity (output gate): the solution must parse under the canonical
    # standalone tla2sany. A real parse failure is a hard FAIL, distinct from a
    # proof that fails to verify — flagged with SANY_INVALID_MARKER so the runner
    # records a `sany_valid` bit. "unavailable" (tooling absent) is fail-open.
    sany_status, sany_detail = check_sany_valid(filepath)
    if sany_status == "unavailable" and sany_detail:
        warnings.append((0, f"SANY validity check skipped ({sany_detail[:160]})"))

    for _line_num, desc in warnings:
        msg = desc.removeprefix("WARNING: ")
        emit(f"  WARNING: {msg}")

    if real_issues:
        for line_num, desc in real_issues:
            emit(f"  Line {line_num}: {desc}")
    else:
        emit("  No cheating detected.")

    # --- Step 3: Verdict — BINARY pass/fail via the A/B/C gate framework ------
    emit()
    emit("=" * 60)
    emit("VERDICT")
    emit("=" * 60)

    # Legacy-only signals not yet a tlacheck vector (L1 preamble byte-match,
    # agent-added PROOF OMITTED), computed with the same detectors the legacy
    # path uses, so the gates capture everything the old checker did.
    legacy_preamble_modified = False
    legacy_proof_omitted = False
    try:
        with open(filepath) as _f:
            _sol_text = _f.read()
        if args.level == 1:
            _main = get_main_version(filepath)
            if _main:
                _main_lines = _main.split("\n")
                _po = find_proof_obvious_line(_main_lines)
                if _po is not None:
                    _cur = _sol_text.split("\n")
                    legacy_preamble_modified = bool(detect_preamble_modification(_main_lines, _cur, _po))
                    legacy_proof_omitted = bool(detect_proof_omitted("\n".join(_cur[_po:])))
        else:
            legacy_proof_omitted = bool(detect_proof_omitted(_sol_text))
    except Exception:
        pass

    # The gate framework (src/tlacheck/gates.py) is the authoritative grader:
    # PASS iff identity AND discharge AND trust. "Cheating" is NOT a separate verdict
    # — it is just a gate failing, so the outcome is binary PASS / FAIL.
    grade_passed, grade_reasons, grade_gates, grade_cheat_checks = True, [], [], []
    try:
        from tlacheck.gates import from_tlacheck, grade

        _gr = grade(
            from_tlacheck(
                engine_result,
                tlapm_obligations_proved=(not obligation_failed and tlapm_exit in (0, 11)),
                n_missing=n_missing,
                sany_valid=(sany_status != "invalid"),
                preamble_modified=legacy_preamble_modified,
                proof_omitted=legacy_proof_omitted,
            )
        )
        grade_passed, grade_reasons = _gr.passed, _gr.reasons
        grade_gates = [g.value for g in _gr.failed_gates()]
        # Failing integrity checks (tamper/admit) distinguish a cheat from an
        # honest incomplete proof — surfaced as a marker for the runner's report.
        grade_cheat_checks = _gr.failed_integrity_checks()
    except Exception as e:  # never let the grader crash the check
        grade_reasons = [f"gate framework unavailable ({e}); fell back to legacy verdict"]
        grade_passed = None  # signal: use legacy verdict alone

    # Safety net during migration: the legacy path must also agree before we
    # report PASS, so the consolidated grader can never be LESS strict than the
    # checker it replaces. Validated equal on a real-solution corpus; kept until
    # the legacy detectors are retired.
    legacy_pass = (not real_issues) and (sany_status != "invalid") and tlapm_passed
    passed = legacy_pass if grade_passed is None else (grade_passed and legacy_pass)

    if passed:
        exit_code = 0
        emit("  PASS — target goal genuinely proved (identity and discharge and trust)")
    else:
        exit_code = 1
        emit("  FAIL")
        for reason in grade_reasons:
            emit(f"    {reason}")
        if sany_status == "invalid":
            emit(f"    {SANY_INVALID_MARKER} {sany_detail[:200]}")
        if grade_gates:
            emit(f"  GATES-FAILED: {','.join(grade_gates)}")
        if grade_cheat_checks:
            emit(f"  CHEAT-DETECTED: {','.join(grade_cheat_checks)}")
        if grade_passed and not legacy_pass:
            emit("  FAIL: legacy safety-net flagged a failure the gates missed — investigate divergence")

    # Write result file
    print(f"\nResult written to: {output_path}")
    write_result_and_exit(exit_code)


if __name__ == "__main__":
    main()
