"""
Run an agent CLI on TLAPS benchmarks to attempt automated proof writing.

For each benchmark:
1. Creates an isolated workspace (fresh git repo with only benchmark files)
2. Runs the chosen backend (codex / claude_code / copilot) with a proof-writing prompt
3. Validates the result with the mode's checker
4. Saves all outputs

Usage:
    python3 runner.py [--backend codex|claude_code|copilot|litellm|pi] [--mode proof-completion|proof-from-scratch] \\
                      [--model NAME] [--jobs N] [--filter PATTERN] \\
                      [--timeout SECS] [--check-timeout SECS] [--output-dir DIR]
"""

import argparse
import contextlib
import fcntl
import json
import os
import random
import re
import select
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass

from common.container import ContainerConfig, ContainerRunner, ensure_image, forward_env
from evaluator import quota
from evaluator.backends import get_backend, list_backends
from evaluator.backends.base import AgentBackend
from evaluator.modes import get_mode, list_modes
from evaluator.modes.base import Mode
from evaluator.score import (
    SCORERS,
    continuation_interrupted,
    continuation_rate_line,
    is_non_genuine,
    is_pass_with_continuations,
    is_skipped,
    n_non_genuine,
    n_skipped,
    weighted_score,
)
from evaluator.termination import TerminationContext, TerminationReason, classify, startup_error_snippet

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# File at <repo>/src/evaluator/runner.py — ascend two levels for repo root.
REPO_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, "..", ".."))

VERDICT_ICONS = {"PASS": "✅", "FAIL": "❌", "CHEATING": "⚠️", "TIMEOUT": "⏱️", "ERROR": "💥"}

# Set to True to stream agent output to terminal during container runs
STREAM_AGENT_OUTPUT = True

# Backoff between infra retries (seconds); the last value repeats. Short: the
# observed startup blips clear within seconds-to-minutes.
INFRA_RETRY_BACKOFF = (15, 30, 60)


def resolve_paths():
    """Return (benchmark_root, checker_binary) based on environment.

    Docker: /benchmark + /usr/local/bin/check_proof_bin (set by docker-compose).
    Host:   <repo>/benchmark + <repo>/check_proof_bin.
    """
    if os.path.isdir("/benchmark"):
        return "/benchmark", "/usr/local/bin/check_proof_bin"
    return os.path.join(REPO_ROOT, "benchmark"), os.path.join(REPO_ROOT, "check_proof_bin")


# Persistent tlapm location — /opt/tlapm in docker, ~/.tlapm on host.
TLAPM_PERSISTENT = "/opt/tlapm" if os.path.isdir("/opt/tlapm") else os.path.expanduser("~/.tlapm")
TLAPM_SOURCE = "/tmp/tlapm"


def ensure_tlapm():
    """Ensure tlapm is available at TLAPM_PERSISTENT (host-only fallback)."""
    if os.path.isfile(os.path.join(TLAPM_PERSISTENT, "bin", "tlapm")):
        print(f"tlapm at {TLAPM_PERSISTENT}")
        return
    if not os.path.isdir(TLAPM_SOURCE):
        print(f"ERROR: tlapm not found at {TLAPM_PERSISTENT} or {TLAPM_SOURCE}")
        sys.exit(1)
    print(f"Copying tlapm to {TLAPM_PERSISTENT}...")
    shutil.copytree(TLAPM_SOURCE, TLAPM_PERSISTENT)
    print("Done.")


def find_tlapm_lib(tlapm_path: str) -> str | None:
    """Derive lib path from tlapm binary path. Supports 1.5 and 1.6 layouts."""
    base = os.path.dirname(os.path.dirname(tlapm_path))
    for sub in ["lib/tlapm/stdlib", "lib/tlaps", "lib/tlapm", "lib"]:
        path = os.path.join(base, sub)
        if os.path.isdir(path):
            return path
    return None


def _proc_descendants(root_pid: int) -> list:
    """All live descendant PIDs of root_pid, via a /proc ppid walk."""
    children: dict = {}
    try:
        entries = os.listdir("/proc")
    except OSError:
        return []
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat", "rb") as f:
                data = f.read().decode("latin1")
            # comm (field 2) is parenthesised and may contain spaces; ppid is
            # the 2nd field after the closing ')'.
            ppid = int(data[data.rindex(")") + 2 :].split()[1])
        except (OSError, ValueError, IndexError):
            continue
        children.setdefault(ppid, []).append(int(entry))
    out, stack = [], [root_pid]
    while stack:
        for c in children.get(stack.pop(), []):
            out.append(c)
            stack.append(c)
    return out


def _procs_with_cwd_under(path: str) -> list:
    """PIDs whose cwd is at/under `path`. Catches Isabelle/poly that detach
    from the process group but still run in the benchmark's workspace."""
    base = os.path.realpath(path)
    out = []
    try:
        entries = os.listdir("/proc")
    except OSError:
        return out
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            cwd = os.readlink(f"/proc/{entry}/cwd")
        except OSError:
            continue
        if cwd == base or cwd.startswith(base + os.sep):
            out.append(int(entry))
    return out


def kill_agent_tree(proc, workspace: str):
    """SIGKILL the agent's whole process tree plus any process whose cwd is in
    `workspace` (detached Isabelle/poly). Scoped to THIS benchmark only — it
    never touches processes from other runs (e.g. a concurrent codex run), so
    it is safe to run on a shared host. This is what reliably reaps tlapm's
    Isabelle backend, which leaks `poly` children that the process-group kill
    alone leaves behind."""
    try:
        pid = proc.pid
    except Exception:
        return
    targets = set()
    with contextlib.suppress(Exception):
        targets.update(_proc_descendants(pid))
    with contextlib.suppress(Exception):
        targets.update(_procs_with_cwd_under(workspace))
    targets.add(pid)
    # Process group first (cheap, scoped to our own session).
    with contextlib.suppress(Exception):
        os.killpg(os.getpgid(pid), signal.SIGKILL)
    for t in targets:
        with contextlib.suppress(Exception):
            os.kill(t, signal.SIGKILL)


def _mem_available_gb() -> float | None:
    """MemAvailable in GiB from /proc/meminfo, or None if unreadable."""
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / 1024 / 1024
    except OSError:
        pass
    return None


def wait_for_memory(min_free_gb: float, max_waits: int, log_prefix: str = "") -> bool:
    """Block until MemAvailable >= min_free_gb before launching a heavy agent.

    Guards a no-swap host against OOM when this run shares the machine with
    another memory-hungry run (e.g. concurrent codex): a single ByzantinePaxos
    Isabelle proof can hold ~150GB, so we hold off launching until there's room.
    Returns True once memory is free (or the check is disabled / unreadable),
    False after max_waits (caller proceeds anyway rather than abort)."""
    if min_free_gb <= 0:
        return True
    waits = 0
    while True:
        avail = _mem_available_gb()
        if avail is None or avail >= min_free_gb:
            return True
        waits += 1
        if waits > max_waits:
            print(
                f"{log_prefix}low memory ({avail:.0f}GB < {min_free_gb:.0f}GB) "
                f"after {max_waits} waits — launching anyway",
                flush=True,
            )
            return True
        print(
            f"{log_prefix}waiting for memory: {avail:.0f}GB free < "
            f"{min_free_gb:.0f}GB needed (wait {waits}/{max_waits})",
            flush=True,
        )
        time.sleep(60)


_summary_lock = threading.Lock()


@dataclass
class WorkItem:
    """A single (benchmark, backend, mode) task fed to the worker pool."""

    benchmark_path: str
    output_dir: str
    timeout: int
    check_timeout: int
    backend: AgentBackend
    mode: Mode
    tlapm_path: str
    tlapm_lib: str
    # Quota gate (Claude Max subscription). usage_script=None disables it.
    usage_script: str | None = None
    quota_5h: float = 0
    quota_7d: float = 0
    quota_max_waits: int = 0
    # Memory gate: hold off launching the agent until this many GB are free
    # (0 = off). Guards a no-swap host against OOM under concurrent heavy runs.
    min_free_gb: float = 0
    # Container mode: run agent inside Docker container
    use_container: bool = False
    # Extra agent attempts after a transient startup/infra failure (INFRA_ERROR
    # with 0 output tokens); 0 disables retrying (the failure still ends ERROR).
    infra_retries: int = 3
    # Continuation rounds after a genuine non-PASS: re-run the agent in the SAME
    # workspace so it builds on its own partial proof (see _run_continuations).
    # 0 disables. pass@1 (check_verdict) is unaffected either way.
    max_continuations: int = 0


def _make_canonical_dir(name_no_ext: str, benchmark_path: str, basename: str, deps: list[str]) -> str:
    canonical_dir = tempfile.mkdtemp(prefix=f"canon_{name_no_ext}_")
    try:
        shutil.copy2(benchmark_path, os.path.join(canonical_dir, basename))
        for dep in deps:
            shutil.copy2(dep, os.path.join(canonical_dir, os.path.basename(dep)))
        return canonical_dir
    except Exception:
        shutil.rmtree(canonical_dir, ignore_errors=True)
        raise


def _make_workspace(backend_name: str, name_no_ext: str, benchmark_path: str, basename: str, deps: list[str]) -> str:
    """Fresh isolated workspace: benchmark + dependencies in a git repo (the
    baseline commit is the cheating check's reference point)."""
    workspace = tempfile.mkdtemp(prefix=f"{backend_name}_bench_{name_no_ext}_")
    try:
        shutil.copy2(benchmark_path, os.path.join(workspace, basename))
        for dep in deps:
            shutil.copy2(dep, os.path.join(workspace, os.path.basename(dep)))
        subprocess.run(["git", "init"], capture_output=True, cwd=workspace)
        subprocess.run(["git", "add", "."], capture_output=True, cwd=workspace)
        subprocess.run(
            ["git", "commit", "-m", "initial benchmark"],
            capture_output=True,
            cwd=workspace,
            env={
                **os.environ,
                "GIT_AUTHOR_NAME": "bench",
                "GIT_AUTHOR_EMAIL": "bench@bench",
                "GIT_COMMITTER_NAME": "bench",
                "GIT_COMMITTER_EMAIL": "bench@bench",
            },
        )
        return workspace
    except Exception:
        shutil.rmtree(workspace, ignore_errors=True)
        raise


@dataclass
class AgentRunOutcome:
    """What _run_agent_with_retries leaves behind for the caller to grade/record."""

    workspace: str
    canonical_dir: str
    transcript: str
    quota_exhausted: bool
    infra_retriable: bool  # still a 0-token infra failure after all retries
    infra_reasons: list[str]


def _run_agent_with_retries(
    item: WorkItem,
    prompt: str,
    agent_dir: str,
    agent_jsonl: str,
    agent_stderr: str,
    result: dict,
    checker_bin: str,
    deps: list[str],
    basename: str,
    name_no_ext: str,
    fixed_workspace: str | None = None,
) -> AgentRunOutcome:
    """One agent-run lifecycle, shared by the first attempt and continuation
    rounds: run the agent (sleeping through hard provider quota caps, see
    quota.run_with_quota_retry), parse its output, classify the termination,
    and retry with backoff while the run died before the model did ANY work
    (INFRA_ERROR + 0 output tokens). A genuine attempt (any output tokens) is
    never re-run.

    Every attempt gets a fresh canonical snapshot: both the agent self-check
    and grader read it, and in local mode the agent can write to the host path,
    so a failed attempt's copy must never leak into a retry or the grader.
    With fixed_workspace=None each attempt also gets a fresh workspace (a
    failed first attempt's partial edits can't leak into a retry); a
    continuation round passes its existing workspace instead — the partial
    proof in it IS the input, and a 0-token startup death can't have touched it.

    Fills result's time_secs / input_tokens / output_tokens / agent_exit /
    error / termination_reason (plus infra_retries / infra_retry_reasons after
    any retries); the caller owns quota/infra exhaustion verdicts and messages.
    time_secs counts only active agent time — quota-retry sleeps (which can be
    hours) and the infra backoff are excluded. Returns the final attempt's
    workspace + canonical snapshot, which the caller must clean up (earlier
    attempts' dirs are cleaned here, including when an attempt raises).
    """
    backend = item.backend
    mode = item.mode
    workspace = fixed_workspace
    canonical_dir = None
    active_secs = 0.0
    quota_exhausted = False
    infra_retriable = False
    infra_reasons: list[str] = []
    transcript = ""
    try:
        for attempt in range(max(item.infra_retries, 0) + 1):
            canonical_dir = _make_canonical_dir(name_no_ext, item.benchmark_path, basename, deps)
            if fixed_workspace is None:
                workspace = _make_workspace(backend.name, name_no_ext, item.benchmark_path, basename, deps)

            wait_for_memory(item.min_free_gb, 120, log_prefix=f"[{name_no_ext}] ")

            # Defaults keep the closure bound to this attempt.
            def _run_once(workspace=workspace, canonical_dir=canonical_dir):
                nonlocal active_secs
                result["error"] = ""
                with contextlib.suppress(FileNotFoundError):
                    os.remove(agent_stderr)
                t0 = time.time()
                if item.use_container:
                    _run_agent_container(
                        item, backend, workspace, agent_dir, agent_jsonl, prompt, result, canonical_dir
                    )
                else:
                    _run_agent_local(
                        item,
                        backend,
                        mode,
                        workspace,
                        agent_dir,
                        agent_jsonl,
                        prompt,
                        result,
                        checker_bin,
                        canonical_dir,
                    )
                active_secs += time.time() - t0

            quota_exhausted = not quota.run_with_quota_retry(
                _run_once,
                lambda: backend.detect_quota_block(agent_jsonl),
                log_prefix=f"[{name_no_ext}] ",
            )
            result["time_secs"] = active_secs

            # Parse agent output on every path — including quota exhaustion — so
            # the result records any tokens the agent did emit (rather than
            # forcing them to 0).
            transcript, input_tokens, output_tokens = backend.parse_output(agent_jsonl)
            result["input_tokens"] = input_tokens
            result["output_tokens"] = output_tokens

            if quota_exhausted:
                break  # quota owns its own retry budget — never infra-retried

            # Tag how the run terminated so an INFRA_ERROR (agent cut short by
            # infrastructure, not a genuine attempt) is distinguishable from a
            # real FAIL — and, when the model did no work, retried right here.
            ctx = TerminationContext(
                backend=backend.name,
                jsonl_path=agent_jsonl,
                agent_exit=result.get("agent_exit"),
                error=result.get("error", ""),
                stderr_path=agent_stderr,
            )
            result["termination_reason"] = classify(ctx)

            # A genuine attempt (any output tokens) is never re-run.
            infra_retriable = result["termination_reason"] == TerminationReason.INFRA_ERROR and output_tokens == 0
            if not infra_retriable:
                break
            infra_reasons.append(startup_error_snippet(ctx))
            if attempt >= item.infra_retries:
                break  # out of retries — the caller records the exhaustion

            _stash_failed_attempt(agent_dir, attempt)
            if fixed_workspace is None:
                shutil.rmtree(workspace, ignore_errors=True)
                workspace = None
            shutil.rmtree(canonical_dir, ignore_errors=True)
            canonical_dir = None
            base = INFRA_RETRY_BACKOFF[min(attempt, len(INFRA_RETRY_BACKOFF) - 1)]
            delay = base + random.uniform(0, base / 2)  # jitter: keep --jobs workers out of lockstep
            print(
                f"[{name_no_ext}] transient infra failure ({infra_reasons[-1]}) — "
                f"retrying in {delay:.0f}s (retry {attempt + 1}/{item.infra_retries})",
                flush=True,
            )
            time.sleep(delay)
    except BaseException:
        # An attempt blew up mid-flight: the caller only ever owns what we
        # return, so don't leak this attempt's dirs (never a fixed workspace).
        if fixed_workspace is None and workspace:
            shutil.rmtree(workspace, ignore_errors=True)
        if canonical_dir:
            shutil.rmtree(canonical_dir, ignore_errors=True)
        raise

    if infra_reasons:
        result["infra_retries"] = attempt  # retries performed (0-based final attempt index)
        result["infra_retry_reasons"] = infra_reasons
    return AgentRunOutcome(workspace, canonical_dir, transcript, quota_exhausted, infra_retriable, infra_reasons)


def _resume_should_skip(result: dict) -> bool:
    """Resume skips genuine completed work: SKIP, first-attempt PASS, or continuation PASS."""
    return is_skipped(result) or (is_pass_with_continuations(result) and not is_non_genuine(result))


def _resume_done_benchmarks(results: list[dict]) -> set[str]:
    return {r["benchmark"] for r in results if _resume_should_skip(r)}


def _continuation_note(result: dict) -> str:
    """One-phrase outcome of a result's continuation rounds ("" without any):
    the round that recovered a PASS, a chain infra/quota-cut before resolving,
    or how many genuine rounds still didn't pass."""
    rounds = result.get("continuations") or []
    if not rounds:
        return ""
    passed = next((r["round"] for r in rounds if r.get("check_verdict") == "PASS"), None)
    if passed is not None:
        return f"PASS on continuation {passed}"
    if continuation_interrupted(result):
        return f"continuation chain cut at round {len(rounds)} (excluded — re-run)"
    return f"no PASS after {len(rounds)} continuation(s)"


def update_summary(results, output_dir, total_benchmarks, backend_name, mode_name):
    """Incrementally update summary.md + results.json with current results."""
    with _summary_lock:
        total = len(results)
        verdicts = {}
        for r in results:
            v = r["check_verdict"]
            verdicts[v] = verdicts.get(v, 0) + 1

        total_input = sum(r.get("input_tokens", 0) for r in results)
        total_output = sum(r.get("output_tokens", 0) for r in results)

        lines = []
        lines.append(f"# {backend_name} on {mode_name}\n")
        lines.append(f"**Date**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        # Match `tlaps-bench score`: SKIP and non-genuine infra/quota-cut runs
        # are excluded from the pass-rate numerator and denominator.
        pass_pct, n_pass, scored = weighted_score(results, SCORERS["equal"])
        n_skip = n_skipped(results)
        non_genuine = n_non_genuine(results)
        pass_line = f"**Pass rate**: {n_pass}/{scored} ({pass_pct:.1f}%)"
        if n_skip:
            pass_line += f" · {n_skip} skipped"
        if non_genuine:
            pass_line += f" · {non_genuine} infra/quota-cut (excluded — re-run)"
        lines.append(f"**Progress**: {total}/{total_benchmarks}")
        lines.append(pass_line)
        # Separate, clearly-labeled metric — the pass rate above stays pass@1.
        cont_line = continuation_rate_line(results, SCORERS["equal"], n_pass)
        if cont_line:
            lines.append(cont_line)
        lines.append(f"**Total tokens**: {total_input:,} input / {total_output:,} output\n")

        lines.append("## Summary\n")
        lines.append("| Verdict | Count |")
        lines.append("|---------|-------|")
        for v in ["PASS", "FAIL", "CHEATING", "TIMEOUT", "ERROR"]:
            count = verdicts.get(v, 0)
            if count > 0:
                icon = VERDICT_ICONS[v]
                lines.append(f"| {icon} {v} | {count} |")
        lines.append("")

        lines.append("## Details\n")
        lines.append("| Benchmark | Verdict | Time | Obligations | Tokens (in/out) | Notes |")
        lines.append("|-----------|---------|------|-------------|-----------------|-------|")
        for r in sorted(results, key=lambda x: x["benchmark"]):
            icon = VERDICT_ICONS.get(r["check_verdict"], "❓")
            notes = r.get("error", "")
            # Flag a SANY-invalid FAIL distinctly (solution rejected by the
            # canonical parser, vs a proof that simply didn't verify).
            if r.get("sany_valid") is False:
                notes = ("SANY✗ " + notes).strip()
            if is_non_genuine(r):
                reason = r.get("termination_reason", "non-genuine")
                notes = (f"{reason} (excluded — re-run) " + notes).strip()
            # Name the tamper/admit check(s) behind a CHEATING verdict so a cheat
            # is distinguishable from an honest incomplete FAIL at a glance.
            if r.get("check_verdict") == "CHEATING" and r.get("cheat_checks"):
                notes = (",".join(r["cheat_checks"]) + " " + notes).strip()
            cont = _continuation_note(r)
            if cont:
                notes = (cont + " " + notes).strip()
            tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
            if "obligations" in r:
                obs = str(r["obligations"])
            elif "obligations_failed" in r:
                obs = f"{r['obligations_failed']}/{r['obligations_total']} failed"
            else:
                obs = ""
            lines.append(
                f"| `{r['benchmark']}` | {icon} {r['check_verdict']} | {r['time_secs']:.0f}s | {obs} | {tokens} | {notes} |"
            )
        lines.append("")

        report = "\n".join(lines)
        report_path = os.path.join(output_dir, "summary.md")
        with open(report_path, "w") as f:
            f.write(report)

        with open(os.path.join(output_dir, "results.json"), "w") as f:
            json.dump(results, f, indent=2)


def run_single_benchmark(item: WorkItem):
    """Run the agent backend on a single benchmark. Returns result dict."""
    backend = item.backend
    mode = item.mode

    rel_path = os.path.relpath(item.benchmark_path, mode.benchmark_dir())
    module_dir = os.path.basename(os.path.dirname(item.benchmark_path))
    basename = os.path.basename(item.benchmark_path)
    name_no_ext = os.path.splitext(basename)[0]

    # Structured result directory: input/, agent/, grading/
    result_dir = os.path.join(item.output_dir, module_dir, name_no_ext)
    input_dir = os.path.join(result_dir, "input")
    agent_dir = os.path.join(result_dir, "agent")
    grading_dir = os.path.join(result_dir, "grading")
    for d in (input_dir, agent_dir, grading_dir):
        os.makedirs(d, exist_ok=True)

    result = {
        "benchmark": rel_path,
        "module": module_dir,
        "theorem": name_no_ext,
        "backend": backend.name,
        "mode": mode.name,
        "agent_exit": -1,
        "check_verdict": "ERROR",
        "time_secs": 0,
        "error": "",
        # How the agent run ended; reclassified after the run (see termination.py).
        # INFRA_ERROR marks a result that was cut short by infrastructure rather
        # than a genuine model attempt, so a FAIL can be filtered/retried.
        "termination_reason": TerminationReason.OK,
    }
    if item.max_continuations > 0:
        # Run-level config, stamped on EVERY result — first-attempt PASSes and
        # non-genuine early exits included — so the continuation metric can
        # state its ≤N budget without guessing from the chains that happened to run.
        result["max_continuations"] = item.max_continuations

    if not quota.wait_for_quota(
        item.usage_script, item.quota_5h, item.quota_7d, item.quota_max_waits,
        log_prefix=f"[{name_no_ext}] ",
    ):
        result["agent_exit"] = -3
        result["error"] = "quota exceeded (max waits reached); skipped"
        result["input_tokens"] = 0
        result["output_tokens"] = 0
        result["termination_reason"] = TerminationReason.QUOTA_EXHAUSTED
        return result

    workspace = None
    canonical_dir = None
    try:
        # Resolve dependencies ONCE — the EXTENDS-closure walk parses files and may
        # warn (e.g. a goal-bearing module reached via the closure), so a second
        # call would just repeat that work and double the stderr noise.
        deps = mode.get_dependencies(item.benchmark_path)

        checker_bin = mode.checker_binary_path()

        # Save input artifacts
        shutil.copy2(item.benchmark_path, os.path.join(input_dir, "benchmark.tla"))
        for dep in deps:
            shutil.copy2(dep, os.path.join(input_dir, os.path.basename(dep)))

        # Build prompt
        prompt = mode.build_prompt(basename, item.tlapm_path, item.tlapm_lib)
        with open(os.path.join(input_dir, "prompt.txt"), "w") as f:
            f.write(prompt)

        # Run the agent
        agent_jsonl = os.path.join(agent_dir, "output.jsonl")
        agent_stderr = os.path.join(agent_dir, "stderr.txt")

        # Infra retry loop: a run cut short before the model did ANY work
        # (INFRA_ERROR + 0 output tokens) says nothing about the model, so it is
        # retried on a fresh workspace instead of graded. Everything else gets
        # exactly one attempt.
        run = _run_agent_with_retries(
            item, prompt, agent_dir, agent_jsonl, agent_stderr, result, checker_bin, deps, basename, name_no_ext
        )
        workspace, canonical_dir = run.workspace, run.canonical_dir

        with open(os.path.join(agent_dir, "transcript.txt"), "w") as f:
            f.write(f"Benchmark: {rel_path}\n")
            f.write(f"Time: {result['time_secs']:.0f}s\n")
            f.write(f"Tokens: {result['input_tokens']:,} input / {result['output_tokens']:,} output\n")
            f.write("=" * 60 + "\n\n")
            f.write(run.transcript)

        solution_path = os.path.join(workspace, basename)
        if os.path.isfile(solution_path):
            shutil.copy2(solution_path, os.path.join(agent_dir, "solution.tla"))

        agent_check_file = os.path.join(workspace, name_no_ext + ".result")
        if os.path.isfile(agent_check_file):
            shutil.copy2(agent_check_file, os.path.join(grading_dir, "agent_check.result"))

        if run.quota_exhausted:
            # Provider hard-capped us past the retry budget. Mark ERROR (retriable
            # via --resume) and skip grading; the artifacts above keep the result
            # dir consistent with a normal run. Tag QUOTA_EXHAUSTED directly — the
            # runner owns the quota signal — rather than running classify() on the
            # no-work, truncated stream, which would misread it as INFRA_ERROR.
            result["agent_exit"] = -3
            result["check_verdict"] = "ERROR"
            result["error"] = "provider usage limit; exhausted quota retries"
            result["termination_reason"] = TerminationReason.QUOTA_EXHAUSTED
            with open(os.path.join(result_dir, "result.json"), "w") as f:
                json.dump(result, f, indent=2)
            return result

        if run.infra_retriable:
            # Out of retries with no genuine attempt made: grading the untouched
            # workspace would turn infra noise into a proof verdict (FAIL, or even
            # a bogus PASS). Mark ERROR (retriable via --resume), skip the grader.
            result["check_verdict"] = "ERROR"
            result["error"] = f"startup/infra failure ({run.infra_reasons[-1]}); exhausted infra retries"
            with open(os.path.join(result_dir, "result.json"), "w") as f:
                json.dump(result, f, indent=2)
            return result

        # Run grader
        check_result_path = os.path.join(grading_dir, "check.result")
        if item.use_container:
            _run_grader_container(item, workspace, basename, grading_dir, check_result_path, result, canonical_dir)
        else:
            _run_grader_local(item, workspace, basename, grading_dir, check_result_path, result, canonical_dir)

        # Opt-in continuation rounds: a genuine non-PASS keeps its workspace and
        # the agent is asked to build on its own partial proof. The pass@1 fields
        # above stay untouched; rounds are recorded under result["continuations"].
        if item.max_continuations > 0 and result["check_verdict"] != "PASS" and not is_non_genuine(result):
            _run_continuations(item, workspace, result, result_dir, basename, name_no_ext, deps, checker_bin)

        # Write per-benchmark result.json
        with open(os.path.join(result_dir, "result.json"), "w") as f:
            json.dump(result, f, indent=2)

    finally:
        if workspace:
            shutil.rmtree(workspace, ignore_errors=True)
        if canonical_dir:
            shutil.rmtree(canonical_dir, ignore_errors=True)

    return result


def _stash_failed_attempt(agent_dir: str, attempt: int) -> None:
    """Move a failed attempt's raw outputs to agent/attempts/attempt-N/: the
    retry starts clean (no stale stderr.txt) and the evidence stays debuggable."""
    dest = os.path.join(agent_dir, "attempts", f"attempt-{attempt}")
    os.makedirs(dest, exist_ok=True)
    for fname in ("output.jsonl", "stderr.txt"):
        src = os.path.join(agent_dir, fname)
        if os.path.isfile(src):
            shutil.move(src, os.path.join(dest, fname))


def _run_continuations(
    item: WorkItem,
    workspace: str,
    result: dict,
    result_dir: str,
    basename: str,
    name_no_ext: str,
    deps: list[str],
    checker_bin: str,
) -> None:
    """Continuation rounds (--max-continuations, off by default).

    A genuine non-PASS mixes two outcomes: the agent stopped early (declared
    itself done with a repairable partial proof still in the file) or it truly
    cannot solve the task. Each round re-runs the agent in the SAME workspace —
    the partial proof is still there — with a continuation prompt telling it to
    build on that prior work, then re-grades; rounds stop at the first PASS, at
    the --max-continuations budget, or when a round is cut short by infra/quota.
    A chain cut short is interrupted, not failed: scoring excludes it from the
    continuation rate (see score.continuation_interrupted) and --resume reruns
    the benchmark.

    The top-level result keeps the FIRST attempt's verdict, so pass@1 is
    reported unchanged; each round's verdict/cost is appended to
    result["continuations"] (the run's ≤N budget is stamped on every result as
    max_continuations at init) and the round's tokens/time accumulate into the
    top-level cost fields (the true cost of the whole chain). Artifacts land in
    <result_dir>/continuations/round-N/, shaped like the agent/ + grading/ dirs.
    """
    mode = item.mode
    prompt = mode.build_continuation_prompt(basename, item.tlapm_path, item.tlapm_lib)
    agent_check_file = os.path.join(workspace, name_no_ext + ".result")
    rounds: list[dict] = result.setdefault("continuations", [])
    for rnd in range(1, item.max_continuations + 1):
        prev_verdict = rounds[-1]["check_verdict"] if rounds else result["check_verdict"]
        print(
            f"[{name_no_ext}] {prev_verdict} — continuing in same workspace "
            f"(round {rnd}/{item.max_continuations})",
            flush=True,
        )
        round_dir = os.path.join(result_dir, "continuations", f"round-{rnd}")
        os.makedirs(round_dir, exist_ok=True)
        with open(os.path.join(round_dir, "prompt.txt"), "w") as f:
            f.write(prompt)
        agent_jsonl = os.path.join(round_dir, "output.jsonl")
        agent_stderr = os.path.join(round_dir, "stderr.txt")
        round_result = {
            "round": rnd,
            "agent_exit": -1,
            "check_verdict": "ERROR",
            "time_secs": 0,
            "error": "",
            "termination_reason": TerminationReason.OK,
        }
        # The in-workspace self-check file survives from the previous round (the
        # agent may want to read what failed), so note its state to copy it as
        # this round's evidence only if this round's agent (re)wrote it.
        check_mtime_before = os.stat(agent_check_file).st_mtime_ns if os.path.isfile(agent_check_file) else None

        run = _run_agent_with_retries(
            item,
            prompt,
            round_dir,
            agent_jsonl,
            agent_stderr,
            round_result,
            checker_bin,
            deps,
            basename,
            name_no_ext,
            fixed_workspace=workspace,
        )
        try:
            result["time_secs"] += round_result["time_secs"]
            result["input_tokens"] += round_result["input_tokens"]
            result["output_tokens"] += round_result["output_tokens"]
            if run.quota_exhausted:
                round_result["agent_exit"] = -3
                round_result["error"] = "provider usage limit; exhausted quota retries"
                round_result["termination_reason"] = TerminationReason.QUOTA_EXHAUSTED
            elif run.infra_retriable:
                round_result["error"] = f"startup/infra failure ({run.infra_reasons[-1]}); exhausted infra retries"

            with open(os.path.join(round_dir, "transcript.txt"), "w") as f:
                f.write(run.transcript)
            solution_path = os.path.join(workspace, basename)
            if os.path.isfile(solution_path):
                shutil.copy2(solution_path, os.path.join(round_dir, "solution.tla"))
            check_mtime_after = os.stat(agent_check_file).st_mtime_ns if os.path.isfile(agent_check_file) else None
            if check_mtime_after is not None and check_mtime_after != check_mtime_before:
                shutil.copy2(agent_check_file, os.path.join(round_dir, "agent_check.result"))

            # Same rule as the first attempt: never grade a round the model
            # never got to work on (quota cap or 0-token startup death).
            cut_short = run.quota_exhausted or run.infra_retriable
            if not cut_short:
                check_result_path = os.path.join(round_dir, "check.result")
                if item.use_container:
                    _run_grader_container(
                        item, workspace, basename, round_dir, check_result_path, round_result, run.canonical_dir
                    )
                else:
                    _run_grader_local(
                        item, workspace, basename, round_dir, check_result_path, round_result, run.canonical_dir
                    )
        finally:
            shutil.rmtree(run.canonical_dir, ignore_errors=True)

        rounds.append(round_result)
        if round_result["check_verdict"] == "PASS":
            print(f"[{name_no_ext}] recovered: PASS on continuation round {rnd}", flush=True)
            break
        if cut_short:
            break


def _run_agent_container(
    item: WorkItem,
    backend,
    workspace: str,
    agent_dir: str,
    agent_jsonl: str,
    prompt: str,
    result: dict,
    canonical_dir: str | None = None,
) -> None:
    """Run agent inside a Docker container with live output streaming."""
    runner = ContainerRunner()
    cmd = backend.build_command("/workspace", "/results")

    config = ContainerConfig(
        workspace=workspace,
        result_dir=agent_dir,  # mount only agent/ subdir as /results
        # Same canonical snapshot the grader reads, bind-mounted read-only so the
        # agent's own check_proof_bin runs the identical cheat oracle the grader will.
        benchmark_dir=canonical_dir or "",
        env=forward_env(backend.env_keys, model=getattr(backend, "model", None)),
        firewall_hosts=backend.firewall_hosts(),
        install_script=backend.install_script,
        credential_mounts=backend.get_credential_mounts(),
    )
    if canonical_dir:
        config.env["TLAPS_BENCHMARK_DIR"] = "/benchmark"
    # Self-check uses the SAME tlapm budget as the grader (item.check_timeout),
    # so a proof near the time boundary can't pass the agent's check yet time out
    # at grading.
    config.env["TLAPS_CHECK_TIMEOUT"] = str(item.check_timeout)

    timeout = item.timeout if item.timeout and item.timeout > 0 else None
    container_run = None
    try:
        container_run = runner.run(config, cmd, stdin_data=prompt)
        proc = container_run.proc
        assert proc.stdout is not None  # Popen created with stdout=PIPE

        # Make stderr non-blocking to prevent pipe deadlock (>64KB stderr blocks agent)
        if proc.stderr:
            flags = fcntl.fcntl(proc.stderr, fcntl.F_GETFL)
            fcntl.fcntl(proc.stderr, fcntl.F_SETFL, flags | os.O_NONBLOCK)

        stderr_chunks: list[str] = []

        # Stream stdout to file in real-time (and stderr separately)
        with open(agent_jsonl, "w") as jsonl_f:
            deadline = (time.time() + timeout) if timeout else None
            while True:
                # Poll with 5s timeout so deadline is checked even if agent hangs
                ready, _, _ = select.select([proc.stdout], [], [], 5.0)
                # Drain stderr opportunistically
                if proc.stderr:
                    try:
                        chunk = proc.stderr.read()
                        if chunk:
                            stderr_chunks.append(chunk)
                    except (OSError, BlockingIOError):
                        pass
                if ready:
                    line = proc.stdout.readline()
                    if not line and proc.poll() is not None:
                        break
                    if line:
                        jsonl_f.write(line)
                        jsonl_f.flush()
                        if STREAM_AGENT_OUTPUT:
                            sys.stdout.write(line)
                            sys.stdout.flush()
                elif proc.poll() is not None:
                    break
                if deadline and time.time() > deadline:
                    runner.kill(container_run)
                    result["agent_exit"] = -1
                    result["error"] = f"{backend.name} timeout after {item.timeout}s"
                    return

        result["agent_exit"] = proc.returncode
        # Drain any remaining stderr
        if proc.stderr:
            try:
                remaining = proc.stderr.read()
                if remaining:
                    stderr_chunks.append(remaining)
            except (OSError, BlockingIOError):
                pass
        stderr = "".join(stderr_chunks)
        if stderr:
            with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
                f.write(stderr)
        if proc.returncode == 137:
            result["error"] = "container OOM killed (exit 137)"
    except Exception as e:
        result["agent_exit"] = -2
        result["error"] = str(e)
        if container_run:
            runner.kill(container_run)
    finally:
        runner.cleanup_credential_tmps()


def _run_agent_local(
    item: WorkItem,
    backend,
    mode,
    workspace: str,
    agent_dir: str,
    agent_jsonl: str,
    prompt: str,
    result: dict,
    checker_bin: str,
    canonical_dir: str | None = None,
) -> None:
    """Run agent as a local subprocess (existing behavior)."""
    cmd = backend.build_command(workspace, agent_dir)
    shell_cmd = "source ~/.zshrc 2>/dev/null; source ~/.bashrc 2>/dev/null; exec " + " ".join(
        shlex.quote(c) for c in cmd
    )

    _to = item.timeout if item.timeout and item.timeout > 0 else None
    timed_out = {"v": False}
    proc = None

    agent_env = dict(os.environ)
    checker_dir = os.path.dirname(os.path.abspath(checker_bin))
    agent_env["PATH"] = checker_dir + os.pathsep + agent_env.get("PATH", "")
    sany_run_sh = os.path.join(REPO_ROOT, "src", "dataset", "sany-dump", "run.sh")
    if os.path.isfile(sany_run_sh):
        agent_env["SANY_RUN_SH"] = sany_run_sh
    # Point the agent's own check_proof_bin at the same canonical snapshot the
    # grader reads, so its self-check is the identical cheat oracle (no host
    # /benchmark mount exists, so the env var is how the checker discovers it).
    if canonical_dir:
        agent_env["TLAPS_BENCHMARK_DIR"] = canonical_dir
    # Same tlapm budget the grader uses, so the discharge verdict matches.
    agent_env["TLAPS_CHECK_TIMEOUT"] = str(item.check_timeout)

    try:
        with open(agent_jsonl, "w") as jsonl_f:
            proc = subprocess.Popen(
                ["bash", "-c", shell_cmd],
                stdin=subprocess.PIPE,
                stdout=jsonl_f,
                stderr=subprocess.PIPE,
                text=True,
                cwd=workspace,
                env=agent_env,
                start_new_session=True,
            )

            def _watchdog():
                timed_out["v"] = True
                kill_agent_tree(proc, workspace)

            timer = threading.Timer(_to, _watchdog) if _to else None
            if timer:
                timer.daemon = True
                timer.start()
            try:
                _bt = (_to + 600) if _to else None
                _, stderr = proc.communicate(input=prompt, timeout=_bt)
            except subprocess.TimeoutExpired:
                timed_out["v"] = True
                kill_agent_tree(proc, workspace)
                with contextlib.suppress(Exception):
                    proc.wait(timeout=30)
                stderr = ""
            finally:
                if timer:
                    timer.cancel()
        result["agent_exit"] = proc.returncode
        if stderr:
            with open(os.path.join(agent_dir, "stderr.txt"), "w") as f:
                f.write(stderr)
        if timed_out["v"]:
            result["agent_exit"] = -1
            result["error"] = f"{backend.name} timeout after {item.timeout}s"
            kill_agent_tree(proc, workspace)
    except Exception as e:
        result["agent_exit"] = -2
        result["error"] = str(e)
        if proc is not None:
            kill_agent_tree(proc, workspace)


def _run_grader_container(
    item: WorkItem,
    workspace: str,
    basename: str,
    grading_dir: str,
    check_result_path: str,
    result: dict,
    canonical_dir: str | None = None,
) -> None:
    """Run grader inside a Docker container (check_proof_bin lives in the image)."""
    runner = ContainerRunner()
    mode = item.mode

    # Use container path for checker binary (not host path)
    old_binary = mode._checker_binary
    mode._checker_binary = "/usr/local/bin/check_proof_bin"
    check_cmd = mode.checker_command(
        "/workspace",
        basename,
        "/results/check.result",
        item.check_timeout,
        benchmark_dir="/benchmark",  # tamper-proof read-only mount
    )
    mode._checker_binary = old_binary
    config = ContainerConfig(
        workspace=workspace,
        result_dir=grading_dir,
        # The same canonical snapshot the agent self-checked against (exactly
        # {target}.tla + deps), NOT the whole module dir.
        benchmark_dir=canonical_dir or os.path.dirname(item.benchmark_path),
    )
    config.env["GIT_CONFIG_COUNT"] = "1"
    config.env["GIT_CONFIG_KEY_0"] = "safe.directory"
    config.env["GIT_CONFIG_VALUE_0"] = "/workspace"
    try:
        exit_code, stdout, stderr = runner.run_with_output(config, check_cmd, timeout=item.check_timeout + 60)
        with open(os.path.join(grading_dir, "check_debug.txt"), "w") as dbg:
            dbg.write(f"exit code: {exit_code}\n")
            dbg.write(f"stdout:\n{stdout}\n")
            dbg.write(f"stderr:\n{stderr}\n")
        _parse_grader_result(exit_code, stdout, result)
    except subprocess.TimeoutExpired:
        result["check_verdict"] = "TIMEOUT"
    except Exception as e:
        result["check_verdict"] = "ERROR"
        result["error"] = str(e)
    finally:
        runner.cleanup_credential_tmps()


def _run_grader_local(
    item: WorkItem,
    workspace: str,
    basename: str,
    grading_dir: str,
    check_result_path: str,
    result: dict,
    canonical_dir: str | None = None,
) -> None:
    """Run grader on host (local mode)."""
    mode = item.mode
    sany_run_sh = os.path.join(REPO_ROOT, "src", "dataset", "sany-dump", "run.sh")

    check_cmd = mode.checker_command(
        workspace,
        basename,
        check_result_path,
        item.check_timeout,
        # The same canonical snapshot the agent self-checked against (exactly
        # {target}.tla + deps), NOT the whole module dir.
        benchmark_dir=canonical_dir or os.path.dirname(item.benchmark_path),
    )
    try:
        check_env = dict(os.environ)
        if os.path.isfile(sany_run_sh):
            check_env["SANY_RUN_SH"] = sany_run_sh
        check_proc = subprocess.run(
            check_cmd,
            capture_output=True,
            text=True,
            timeout=item.check_timeout + 60,
            cwd=workspace,
            env=check_env,
        )
        with open(os.path.join(grading_dir, "check_debug.txt"), "w") as dbg:
            dbg.write(f"exit code: {check_proc.returncode}\n")
            dbg.write(f"stdout:\n{check_proc.stdout}\n")
            dbg.write(f"stderr:\n{check_proc.stderr}\n")
        _parse_grader_result(check_proc.returncode, check_proc.stdout, result)
    except subprocess.TimeoutExpired:
        result["check_verdict"] = "TIMEOUT"
    except Exception as e:
        result["check_verdict"] = "ERROR"
        result["error"] = str(e)


def _parse_grader_result(exit_code: int, stdout: str, result: dict) -> None:
    """Parse grader exit code + stdout into result dict."""
    # The merged checker is binary: exit 0 = PASS, 1 = FAIL (a cheat is just a
    # FAIL, not a separate exit code). Anything else is unexpected → ERROR.
    if exit_code == 0:
        result["check_verdict"] = "PASS"
    elif exit_code == 1:
        result["check_verdict"] = "FAIL"
    else:
        result["check_verdict"] = "ERROR"
    result["sany_valid"] = "[SANY-INVALID]" not in (stdout or "")
    # Which gate(s) failed (the grade is binary; this keeps the analysis signal).
    gm = re.search(r"GATES-FAILED:\s*([^\n]+)", stdout or "")
    if gm:
        result["failed_gates"] = [g.strip() for g in gm.group(1).split(",") if g.strip()]
    # A FAIL whose failing checks include an integrity (tamper/admit) check is a
    # cheat, not an honest incomplete proof — relabel it for the human-facing
    # report so the two are distinguishable at a glance. The checker emits
    # CHEAT-DETECTED with the failing integrity-check names; the grade itself
    # stays binary (the PASS/FAIL exit code is untouched).
    if result["check_verdict"] == "FAIL":
        cm = re.search(r"CHEAT-DETECTED:\s*([^\n]+)", stdout or "")
        if cm:
            result["check_verdict"] = "CHEATING"
            result["cheat_checks"] = [c.strip() for c in cm.group(1).split(",") if c.strip()]
    ob_matches = re.findall(r"All (\d+) obligation", stdout)
    if ob_matches:
        result["obligations"] = int(ob_matches[-1])
    else:
        fail_match = re.search(r"(\d+)/(\d+) obligation", stdout)
        if fail_match:
            result["obligations_failed"] = int(fail_match.group(1))
            result["obligations_total"] = int(fail_match.group(2))


# A one-word prompt that needs no tools and no workspace files — keeps the
# preflight model call as cheap and as deterministic as possible.
PREFLIGHT_PROMPT = "Reply with the single word: ok. Do not use any tools."


def _run_preflight(backend) -> None:
    """Validate a backend end-to-end (install + auth + model + firewall) before
    the run, aborting the process on failure.

    Runs the backend's real build_command inside a throwaway container — same
    install script, env, credentials and firewall as a real run — on a one-word
    prompt. A broken model id, an unknown CLI flag, missing credentials, or an
    auth host the firewall blocks all surface here in ~1 min, instead of as a
    full sweep of silent 0-token FAILs.
    """
    runner = ContainerRunner()
    workspace = tempfile.mkdtemp(prefix="preflight_ws_")
    result_dir = tempfile.mkdtemp(prefix="preflight_res_")
    # Mirror a real run's workspace: the per-benchmark flow git-inits it, and
    # some CLIs (e.g. codex exec) refuse to run outside a git repo. Without this
    # the preflight would false-fail for those backends.
    subprocess.run(["git", "init"], capture_output=True, cwd=workspace)
    try:
        config = ContainerConfig(
            workspace=workspace,
            result_dir=result_dir,
            env=forward_env(backend.env_keys, model=getattr(backend, "model", None)),
            firewall_hosts=backend.firewall_hosts(),
            install_script=backend.install_script,
            credential_mounts=backend.get_credential_mounts(),
        )
        cmd = backend.build_command("/workspace", "/results")
        print(f"Preflight: validating '{backend.name}' (install + auth + model + firewall)...", flush=True)
        runner.run_preflight(config, cmd, PREFLIGHT_PROMPT)
        print("Preflight: OK", flush=True)
    except RuntimeError as e:
        print(f"ERROR: {e}")
        print("Aborting before the run. Re-run with --skip-preflight to bypass this check.")
        sys.exit(1)
    finally:
        shutil.rmtree(workspace, ignore_errors=True)
        shutil.rmtree(result_dir, ignore_errors=True)


def main():
    parser = argparse.ArgumentParser(description="Run an agent CLI on TLAPS benchmarks")
    parser.add_argument("--backend", default="codex", choices=list_backends(), help="Agent backend (default: codex)")
    parser.add_argument("--mode", default="proof-completion", choices=list_modes(), help="Benchmark mode (default: proof-completion)")
    parser.add_argument("--model", default=None, help="Override the backend default model")
    parser.add_argument("--jobs", type=int, default=1, help="Parallel agent runs")
    parser.add_argument("--filter", default=None, help="Only run benchmarks matching pattern")
    parser.add_argument(
        "--timeout",
        type=int,
        default=28800,
        help="Agent timeout per benchmark in seconds (default: 28800 = 8h; 0 = no limit)",
    )
    parser.add_argument(
        "--check-timeout", type=int, default=600, help="Checker timeout per benchmark in seconds (default: 600)"
    )
    parser.add_argument("--output-dir", default=None, help="Output directory")
    # Proactive quota gate. Before launching an agent, pause when the backend's
    # subscription usage is over threshold, sleeping until the window resets. The
    # backend supplies its own usage probe and default thresholds; --quota-5h/7d
    # override them, 0 disables a window's check.
    parser.add_argument(
        "--quota-5h",
        type=float,
        default=None,
        help="Pause when 5-hour usage exceeds this %% (default: backend-specific; 0 = off)",
    )
    parser.add_argument(
        "--quota-7d",
        type=float,
        default=None,
        help="Pause when 7-day usage exceeds this %% (default: backend-specific; 0 = off)",
    )
    parser.add_argument(
        "--quota-max-waits",
        type=int,
        default=6,
        help="Max window resets to sleep through before aborting a benchmark (default: 6)",
    )
    parser.add_argument(
        "--usage-script",
        default=None,
        help="Override the backend's usage probe with a custom script path",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Reuse --output-dir: skip benchmarks already SKIP or genuinely passed there (first-attempt or continuation), run the rest",
    )
    parser.add_argument(
        "--min-free-gb",
        type=float,
        default=0,
        help="Hold off launching an agent until this many GB RAM are free "
        "(0 = off). Use on a no-swap host shared with another heavy run.",
    )
    parser.add_argument(
        "--infra-retries",
        type=int,
        default=3,
        help="Extra agent attempts after a transient startup/infrastructure failure "
        "(agent died with 0 output tokens), so 3 = up to 4 attempts total "
        "(default: 3; 0 = no retries, the failure still ends as ERROR)",
    )
    parser.add_argument(
        "--max-continuations",
        type=int,
        default=0,
        help="After a genuine non-PASS verdict, re-run the agent up to N more times in the "
        "SAME workspace with a continuation prompt (build on its own partial proof), "
        "stopping at the first PASS. The first attempt's verdict still scores pass@1; "
        "continuation rounds are recorded and reported separately (default: 0 = off)",
    )
    parser.add_argument(
        "--no-container",
        action="store_true",
        help="Run agent locally instead of inside a Docker container",
    )
    parser.add_argument(
        "--force-build",
        action="store_true",
        help="Force rebuild the Docker base image before running",
    )
    parser.add_argument(
        "--skip-preflight",
        action="store_true",
        help="Skip the container preflight check (validate install + auth + model + firewall "
        "on a trivial prompt before the run). Container mode only.",
    )
    args = parser.parse_args()

    backend = get_backend(args.backend, model=args.model)

    auth_err = backend.check_auth()
    if auth_err:
        print(f"ERROR: {auth_err}")
        sys.exit(1)

    # Container mode is default; --no-container disables it
    use_container = not args.no_container

    if use_container:
        # In container mode, tlapm and checker are inside the image.
        # Use container-side paths for prompts.
        tlapm_root = "/opt/tlapm"
        tlapm_lib = "/opt/tlapm/lib/tlapm/stdlib"
        benchmark_root = os.path.join(REPO_ROOT, "benchmark")
        checker_binary = os.path.join(REPO_ROOT, "check_proof_bin")
        mode = get_mode(args.mode, benchmark_root, checker_binary)

        ensure_image(force=args.force_build)
        print("Container mode: ON (image: tlaps-bench-base)")

        # Preflight: validate install + auth + model + firewall on a trivial
        # prompt before committing to the full run. A broken backend (bad model
        # id, unknown CLI flag, missing credentials, or an auth host the
        # firewall blocks) otherwise produces a whole sweep of silent 0-token
        # FAILs that look like honest "couldn't prove it" results.
        if not args.skip_preflight:
            _run_preflight(backend)
    else:
        # Local mode: require tlapm and checker on host
        ensure_tlapm()
        tlapm_root = TLAPM_PERSISTENT
        tlapm_bin = os.path.join(tlapm_root, "bin", "tlapm")
        tlapm_lib = find_tlapm_lib(tlapm_bin)
        if not tlapm_lib:
            print(f"ERROR: tlapm lib not found near {tlapm_bin}")
            sys.exit(1)

        benchmark_root, checker_binary = resolve_paths()
        mode = get_mode(args.mode, benchmark_root, checker_binary)

    # results/<mode>/<backend>/<ts>/  (mode first, then agent)
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        if os.path.isdir("/result"):
            output_dir = os.path.join("/result", mode.name, backend.name, timestamp)
        else:
            output_dir = os.path.join(REPO_ROOT, "results", mode.name, backend.name, timestamp)
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    print(f"Backend: {backend.name}" + (f" (model={args.model})" if args.model else ""))
    print(f"Mode:   {mode.name} — {mode.description}")
    print(f"Output:  {output_dir}")

    # Proactive quota gate. The backend supplies its usage probe and default
    # thresholds; --quota-5h/7d override them. Gating stays off when the backend
    # has no probe, both thresholds are 0, or the probe can't read usage (API-key
    # auth, no subscription) — it never blocks a run it can't measure.
    b5, b7 = backend.default_quota()
    quota_5h = b5 if args.quota_5h is None else args.quota_5h
    quota_7d = b7 if args.quota_7d is None else args.quota_7d
    usage_script = None
    script_rel = backend.usage_script()
    candidate = args.usage_script or (os.path.join(REPO_ROOT, script_rel) if script_rel else None)
    if candidate and (quota_5h > 0 or quota_7d > 0):
        if os.path.isfile(candidate):
            usage = quota.fetch_usage(candidate)
            if usage is not None:
                usage_script = candidate
                u5 = (usage.get("five_hour") or {}).get("utilization", 0)
                u7 = (usage.get("seven_day") or {}).get("utilization", 0)
                print(
                    f"Quota:   gate ON — now 5h={u5}% (limit {quota_5h}%), "
                    f"7d={u7}% (limit {quota_7d}%), max-waits={args.quota_max_waits}"
                )
            else:
                print(
                    "Quota:   gate OFF — usage probe returned no data "
                    "(API-key auth or no subscription usage to read)"
                )
        else:
            print(f"Quota:   gate OFF — usage script not found at {candidate}")

    benchmark_files = mode.get_benchmark_files(args.filter)
    print(f"Found {len(benchmark_files)} benchmarks")

    # Resume: reuse --output-dir, skip benchmarks already genuinely completed
    # there, and seed `results` so the summary stays cumulative across the rerun.
    results = []
    done_pass = set()
    if args.resume:
        prev_json = os.path.join(output_dir, "results.json")
        if os.path.isfile(prev_json):
            with open(prev_json) as f:
                results = json.load(f)
            # Skip genuine PASS (already done) and SKIP (operator-marked
            # frontier benchmarks deliberately excluded from retry). A PASS
            # produced by INFRA_ERROR / QUOTA_EXHAUSTED is non-genuine and must
            # be eligible for rerun.
            done_pass = _resume_done_benchmarks(results)
            # Count with the same predicate the skip decision uses, so the
            # message includes benchmarks solved on a continuation round.
            n_pass = sum(1 for r in results if _resume_should_skip(r) and not is_skipped(r))
            n_skip = n_skipped(results)
            non_genuine = n_non_genuine(results)
            msg = (
                f"Resume: loaded {len(results)} prior results, skipping {n_pass} genuine PASS "
                f"(first-attempt or continuation) + {n_skip} SKIP"
            )
            if non_genuine:
                msg += f"; {non_genuine} infra/quota-cut result(s) eligible for rerun"
            print(msg)
        else:
            print(f"Resume: no prior results.json in {output_dir} — running all")

    work_items = []
    for bf in benchmark_files:
        rel = os.path.relpath(bf, mode.benchmark_dir())
        if rel in done_pass:
            continue
        work_items.append(
            WorkItem(
                benchmark_path=bf,
                output_dir=output_dir,
                timeout=args.timeout,
                check_timeout=args.check_timeout,
                backend=backend,
                mode=mode,
                tlapm_path=tlapm_root,
                tlapm_lib=tlapm_lib,
                usage_script=usage_script,
                quota_5h=quota_5h,
                quota_7d=quota_7d,
                quota_max_waits=args.quota_max_waits,
                min_free_gb=args.min_free_gb,
                use_container=use_container,
                infra_retries=args.infra_retries,
                max_continuations=args.max_continuations,
            )
        )

    start_time = time.time()
    total_benchmarks = len(benchmark_files)
    prior_done = len(results)
    if args.resume:
        print(f"Resume: {len(work_items)} benchmarks left to run")

    if args.jobs == 1:
        for i, item in enumerate(work_items):
            r = run_single_benchmark(item)
            results.append(r)
            icon = VERDICT_ICONS.get(r["check_verdict"], "❓")
            tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
            cont = _continuation_note(r)
            print(
                f"[{prior_done + i + 1}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)"
                + (f" — {cont}" if cont else "")
            )
            update_summary(results, output_dir, total_benchmarks, backend.name, mode.name)
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(run_single_benchmark, item): item for item in work_items}
            for done_count, future in enumerate(as_completed(futures), start=1):
                r = future.result()
                results.append(r)
                icon = VERDICT_ICONS.get(r["check_verdict"], "❓")
                tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
                cont = _continuation_note(r)
                print(
                    f"[{prior_done + done_count}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)"
                    + (f" — {cont}" if cont else "")
                )
                update_summary(results, output_dir, total_benchmarks, backend.name, mode.name)

    total_time = time.time() - start_time

    update_summary(results, output_dir, total_benchmarks, backend.name, mode.name)
    report_path = os.path.join(output_dir, "summary.md")

    print(f"\n{'=' * 60}")
    print(f"Completed in {total_time:.0f}s")
    print(f"Report: {report_path}")

    verdicts = {}
    for r in results:
        v = r["check_verdict"]
        verdicts[v] = verdicts.get(v, 0) + 1
    for v in ["PASS", "FAIL", "CHEATING", "TIMEOUT", "ERROR"]:
        if v in verdicts:
            print(f"  {VERDICT_ICONS.get(v, '❓')} {v}: {verdicts[v]}")
    total_in = sum(r.get("input_tokens", 0) for r in results)
    total_out = sum(r.get("output_tokens", 0) for r in results)
    print(f"  Total tokens: {total_in:,} input / {total_out:,} output")


if __name__ == "__main__":
    main()
