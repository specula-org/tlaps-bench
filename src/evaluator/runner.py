#!/usr/bin/env python3
"""
Run an agent CLI on TLAPS benchmarks to attempt automated proof writing.

For each benchmark:
1. Creates an isolated workspace (fresh git repo with only benchmark files)
2. Runs the chosen backend (codex / claude_code / copilot) with a proof-writing prompt
3. Validates the result with the level's checker
4. Saves all outputs

Usage:
    python3 runner.py [--backend codex|claude_code|copilot] [--level level1|level2] \\
                      [--model NAME] [--jobs N] [--filter PATTERN] \\
                      [--timeout SECS] [--check-timeout SECS] [--output-dir DIR]
"""

import argparse
import glob
import json
import os
import re
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

# Allow `python3 src/evaluator/runner.py` as well as module import.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import contextlib

from backends import get_backend, list_backends  # noqa: E402
from levels import get_level, list_levels  # noqa: E402

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# File at <repo>/src/evaluator/runner.py — ascend two levels for repo root.
REPO_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, "..", ".."))


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


def fetch_usage(usage_script: str) -> dict | None:
    """Return the parsed OAuth usage JSON, or None if unavailable.

    Fails open (returns None) on any error — missing script, API-key-only auth
    with no OAuth token, network failure, bad JSON. Callers treat None as
    "can't tell, proceed", so the quota gate never blocks a run it can't
    measure (e.g. the docker / API-key path).
    """
    if not usage_script or not os.path.isfile(usage_script):
        return None
    try:
        r = subprocess.run(["bash", usage_script], capture_output=True, text=True, timeout=30)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None
    try:
        return json.loads(r.stdout)
    except json.JSONDecodeError:
        return None


def _usage_over(usage: dict, quota_5h: float, quota_7d: float):
    """Return (list of "5h=NN% (limit MM%)" strings, earliest resets_at) for
    any window over its limit. A limit <= 0 disables that window's check."""
    over = []
    resets = []
    for key, limit in (("five_hour", quota_5h), ("seven_day", quota_7d)):
        if limit <= 0:
            continue
        obj = usage.get(key) or {}
        util = obj.get("utilization") or 0
        if util > limit:
            over.append(f"{key}={util}% (limit {limit}%)")
            ra = obj.get("resets_at")
            if ra:
                resets.append(ra)
    earliest = sorted(resets)[0] if resets else None
    return over, earliest


def _secs_until(resets_at: str) -> int:
    """Seconds from now until an ISO-8601 resets_at, + 120s buffer.

    Clamped to [60, 3600]. The 1h cap is a safety net against a skewed system
    clock (this host has shown corrupt process times): a bad time.time() could
    otherwise compute a multi-day sleep. The gate re-polls after each sleep, so
    capping just means an extra usage check, never a missed resume.
    """
    try:
        from datetime import datetime

        dt = datetime.fromisoformat(resets_at)
        secs = int(dt.timestamp() - time.time()) + 120
        return min(max(secs, 60), 3600)
    except Exception:
        return 600


def wait_for_quota(item: "WorkItem", log_prefix: str = "") -> bool:
    """Block until the subscription's 5h/7d usage is under threshold.

    Polls usage_script; if a window is over its limit, sleeps until that
    window's resets_at (+2min), then re-checks. Returns True once under
    threshold (or when gating is disabled / usage can't be measured), or
    False after exceeding quota_max_waits resets (caller should abort).
    """
    if not item.usage_script or (item.quota_5h <= 0 and item.quota_7d <= 0):
        return True
    waits = 0
    while True:
        usage = fetch_usage(item.usage_script)
        if usage is None:
            return True  # fail open — can't measure, don't block
        over, reset_at = _usage_over(usage, item.quota_5h, item.quota_7d)
        if not over:
            return True
        waits += 1
        if waits > item.quota_max_waits:
            print(
                f"{log_prefix}quota over after {item.quota_max_waits} waits "
                f"({', '.join(over)}); aborting this benchmark",
                flush=True,
            )
            return False
        sleep_secs = _secs_until(reset_at) if reset_at else 600
        when = reset_at or f"+{sleep_secs}s"
        print(
            f"{log_prefix}quota over: {', '.join(over)} — sleeping "
            f"{sleep_secs}s until {when} (wait {waits}/{item.quota_max_waits})",
            flush=True,
        )
        time.sleep(sleep_secs)


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
    """A single (benchmark, backend, level) task fed to the worker pool."""

    benchmark_path: str
    output_dir: str
    timeout: int
    check_timeout: int
    backend: object
    level: object
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


def update_summary(results, output_dir, total_benchmarks, backend_name, level_name):
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
        lines.append(f"# {backend_name} on {level_name}\n")
        lines.append(f"**Date**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**Progress**: {total}/{total_benchmarks}")
        lines.append(f"**Total tokens**: {total_input:,} input / {total_output:,} output\n")

        lines.append("## Summary\n")
        lines.append("| Verdict | Count |")
        lines.append("|---------|-------|")
        for v in ["PASS", "FAIL", "CHEATING", "TIMEOUT", "ERROR"]:
            count = verdicts.get(v, 0)
            if count > 0:
                icon = {"PASS": "✅", "FAIL": "❌", "CHEATING": "⚠️", "TIMEOUT": "⏱️", "ERROR": "💥"}[v]
                lines.append(f"| {icon} {v} | {count} |")
        lines.append("")

        lines.append("## Details\n")
        lines.append("| Benchmark | Verdict | Time | Obligations | Tokens (in/out) | Notes |")
        lines.append("|-----------|---------|------|-------------|-----------------|-------|")
        for r in sorted(results, key=lambda x: x["benchmark"]):
            icon = {"PASS": "✅", "FAIL": "❌", "CHEATING": "⚠️", "TIMEOUT": "⏱️", "ERROR": "💥"}.get(
                r["check_verdict"], "❓"
            )
            notes = r.get("error", "")
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
    level = item.level

    rel_path = os.path.relpath(item.benchmark_path, level.benchmark_dir())
    module_dir = os.path.basename(os.path.dirname(item.benchmark_path))
    basename = os.path.basename(item.benchmark_path)
    name_no_ext = os.path.splitext(basename)[0]

    result_dir = os.path.join(item.output_dir, module_dir, name_no_ext)
    os.makedirs(result_dir, exist_ok=True)

    result = {
        "benchmark": rel_path,
        "module": module_dir,
        "theorem": name_no_ext,
        "backend": backend.name,
        "level": level.name,
        "agent_exit": -1,
        "check_verdict": "ERROR",
        "time_secs": 0,
        "error": "",
    }

    # Quota gate: pause before doing any work if the Claude Max subscription
    # is over threshold (sleeps until the window resets, then resumes). Gated
    # here — before workspace setup — so sleeping workers don't hold temp dirs.
    # No-op when gating is disabled or usage can't be measured (codex / API-key
    # auth / docker), in which case it returns True immediately.
    if not wait_for_quota(item, log_prefix=f"[{name_no_ext}] "):
        result["agent_exit"] = -3
        result["error"] = "quota exceeded (max waits reached); skipped"
        result["input_tokens"] = 0
        result["output_tokens"] = 0
        return result

    workspace = tempfile.mkdtemp(prefix=f"{backend.name}_bench_{name_no_ext}_")
    try:
        # Copy benchmark + dependencies into the isolated workspace
        shutil.copy2(item.benchmark_path, os.path.join(workspace, basename))
        for dep in level.get_dependencies(item.benchmark_path):
            shutil.copy2(dep, os.path.join(workspace, os.path.basename(dep)))

        # Init git repo with original files as initial commit (the baseline
        # the cheating check compares against)
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

        # The cheat checker is the baked, root-owned, read-only binary on PATH
        # (/usr/local/bin/check_proof_bin in docker). It is NEVER copied into the
        # agent-writable workspace, so the agent cannot swap it to fake a verdict.
        checker_bin = level.checker_binary_path()

        # Archive the original benchmark
        shutil.copy2(item.benchmark_path, os.path.join(result_dir, "benchmark.tla"))

        # Build prompt
        prompt = level.build_prompt(basename, item.tlapm_path, item.tlapm_lib)
        prompt_file = os.path.join(result_dir, "prompt.txt")
        with open(prompt_file, "w") as f:
            f.write(prompt)

        # Run the agent
        agent_jsonl = os.path.join(result_dir, f"{backend.name}_output.jsonl")
        cmd = backend.build_command(workspace, result_dir)

        # Source shell profile for host env vars (no-op in docker).
        shell_cmd = "source ~/.zshrc 2>/dev/null; source ~/.bashrc 2>/dev/null; exec " + " ".join(
            shlex.quote(c) for c in cmd
        )

        # Memory gate: on a no-swap host shared with another heavy run, hold off
        # launching until there's RAM headroom (no-op when min_free_gb == 0).
        wait_for_memory(item.min_free_gb, 120, log_prefix=f"[{name_no_ext}] ")

        start_time = time.time()
        # timeout <= 0 means no limit.
        _to = item.timeout if item.timeout and item.timeout > 0 else None
        timed_out = {"v": False}
        proc = None
        # Make `check_proof_bin` resolvable on PATH for the agent's self-check
        # without a writable workspace copy. In docker it already lives in
        # /usr/local/bin; on host we prepend the repo root (where the binary is).
        agent_env = dict(os.environ)
        checker_dir = os.path.dirname(os.path.abspath(checker_bin))
        agent_env["PATH"] = checker_dir + os.pathsep + agent_env.get("PATH", "")
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
                    start_new_session=True,  # own process group / session
                )

                # Watchdog is the PRIMARY timeout: at _to it forcibly reaps the
                # agent's whole tree incl. detached Isabelle/poly (process-group
                # kill alone leaves those behind, which is what hung the run and
                # leaked ~150GB). We don't rely on communicate()'s own timeout —
                # it failed to fire when a hung tlapm child held the pipe open.
                def _watchdog():
                    timed_out["v"] = True
                    kill_agent_tree(proc, workspace)

                timer = threading.Timer(_to, _watchdog) if _to else None
                if timer:
                    timer.daemon = True
                    timer.start()
                try:
                    # Backstop timeout 10min past the watchdog so communicate can
                    # never block forever even if a stray pipe holder lingers.
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
                with open(os.path.join(result_dir, "agent_stderr.txt"), "w") as f:
                    f.write(stderr)
            if timed_out["v"]:
                result["agent_exit"] = -1
                result["error"] = f"{backend.name} timeout after {item.timeout}s"
                kill_agent_tree(proc, workspace)  # final sweep
        except Exception as e:
            result["agent_exit"] = -2
            result["error"] = str(e)
            if proc is not None:
                kill_agent_tree(proc, workspace)

        elapsed = time.time() - start_time
        result["time_secs"] = elapsed

        transcript, input_tokens, output_tokens = backend.parse_output(agent_jsonl)
        result["input_tokens"] = input_tokens
        result["output_tokens"] = output_tokens

        transcript_path = os.path.join(result_dir, "transcript.txt")
        with open(transcript_path, "w") as f:
            f.write(f"Benchmark: {rel_path}\n")
            f.write(f"Time: {elapsed:.0f}s\n")
            f.write(f"Tokens: {input_tokens:,} input / {output_tokens:,} output\n")
            f.write("=" * 60 + "\n\n")
            f.write(transcript)

        # Copy all .tla files from workspace (solution + dependencies)
        solution_path = os.path.join(workspace, basename)
        for tla_file in glob.glob(os.path.join(workspace, "*.tla")):
            shutil.copy2(tla_file, os.path.join(result_dir, os.path.basename(tla_file)))
        if os.path.isfile(solution_path):
            shutil.copy2(solution_path, os.path.join(result_dir, "solution.tla"))

        # Copy .result file if the agent ran the checker itself
        result_file = os.path.join(workspace, name_no_ext + ".result")
        if os.path.isfile(result_file):
            shutil.copy2(result_file, os.path.join(result_dir, "agent_check.result"))

        # Run our own checker via the level. The compiled binary now runs the
        # full cheat engine (legacy regex + SANY semantic + incomplete-proof)
        # inline, so a single invocation produces the authoritative verdict.
        check_result_path = os.path.join(result_dir, "check.result")
        cmd = level.checker_command(
            workspace,
            basename,
            check_result_path,
            item.check_timeout,
            benchmark_dir=os.path.dirname(item.benchmark_path),
        )
        try:
            check_proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=item.check_timeout + 60,
                cwd=workspace,
            )
            check_log = os.path.join(result_dir, "check_debug.txt")
            with open(check_log, "w") as dbg:
                dbg.write(f"exit code: {check_proc.returncode}\n")
                dbg.write(f"stdout:\n{check_proc.stdout}\n")
                dbg.write(f"stderr:\n{check_proc.stderr}\n")
            if check_proc.returncode == 0:
                result["check_verdict"] = "PASS"
            elif check_proc.returncode == 2:
                result["check_verdict"] = "CHEATING"
            elif check_proc.returncode == 1:
                result["check_verdict"] = "FAIL"
            else:
                result["check_verdict"] = "ERROR"
            ob_matches = re.findall(r"All (\d+) obligation", check_proc.stdout)
            if ob_matches:
                result["obligations"] = int(ob_matches[-1])
            else:
                fail_match = re.search(r"(\d+)/(\d+) obligation", check_proc.stdout)
                if fail_match:
                    result["obligations_failed"] = int(fail_match.group(1))
                    result["obligations_total"] = int(fail_match.group(2))
        except subprocess.TimeoutExpired:
            result["check_verdict"] = "TIMEOUT"
        except Exception as e:
            result["check_verdict"] = "ERROR"
            result["error"] = str(e)

    finally:
        shutil.rmtree(workspace, ignore_errors=True)

    return result


def main():
    parser = argparse.ArgumentParser(description="Run an agent CLI on TLAPS benchmarks")
    parser.add_argument("--backend", default="codex", choices=list_backends(), help="Agent backend (default: codex)")
    parser.add_argument("--level", default="level1", choices=list_levels(), help="Benchmark level (default: level1)")
    parser.add_argument("--model", default=None, help="Override the backend default model")
    parser.add_argument("--jobs", type=int, default=1, help="Parallel agent runs")
    parser.add_argument("--filter", default=None, help="Only run benchmarks matching pattern")
    parser.add_argument(
        "--timeout", type=int, default=7200, help="Agent timeout per benchmark in seconds (default: 7200; 0 = no limit)"
    )
    parser.add_argument(
        "--check-timeout", type=int, default=600, help="Checker timeout per benchmark in seconds (default: 600)"
    )
    parser.add_argument("--output-dir", default=None, help="Output directory")
    # Quota gate (claude_code + Claude Max subscription only). Pauses before
    # launching an agent when subscription usage is over threshold, sleeping
    # until the window resets. 0 disables a window's check.
    parser.add_argument(
        "--quota-5h", type=float, default=80, help="Pause when 5-hour usage exceeds this %% (default: 80; 0 = off)"
    )
    parser.add_argument(
        "--quota-7d", type=float, default=95, help="Pause when 7-day usage exceeds this %% (default: 95; 0 = off)"
    )
    parser.add_argument(
        "--quota-max-waits",
        type=int,
        default=6,
        help="Max window resets to sleep through before aborting a benchmark (default: 6)",
    )
    parser.add_argument("--usage-script", default=None, help="Path to usage.sh (default: <repo>/scripts/usage.sh)")
    parser.add_argument(
        "--resume", action="store_true", help="Reuse --output-dir: skip benchmarks already PASS there, run the rest"
    )
    parser.add_argument(
        "--min-free-gb",
        type=float,
        default=0,
        help="Hold off launching an agent until this many GB RAM are free "
        "(0 = off). Use on a no-swap host shared with another heavy run.",
    )
    args = parser.parse_args()

    backend = get_backend(args.backend, model=args.model)

    auth_err = backend.check_auth()
    if auth_err:
        print(f"ERROR: {auth_err}")
        sys.exit(1)

    ensure_tlapm()
    # tlapm has two paths the runner tracks separately:
    #   tlapm_root — install root (TLAPM_PERSISTENT). The prompt template
    #                appends `/bin/tlapm` itself, and uses tlapm_root for
    #                "do not modify any files under {tlapm_path}/".
    #   tlapm_bin  — the binary, used by find_tlapm_lib (which derives the
    #                lib dir as two levels above the binary).
    # Conflating the two caused the prompt to expand to
    # `<install_root>/bin/tlapm/bin/tlapm`, which the agent then ran and
    # got "Not a directory" on every tlapm invocation.
    tlapm_root = TLAPM_PERSISTENT
    tlapm_bin = os.path.join(tlapm_root, "bin", "tlapm")
    tlapm_lib = find_tlapm_lib(tlapm_bin)
    if not tlapm_lib:
        print(f"ERROR: tlapm lib not found near {tlapm_bin}")
        sys.exit(1)

    benchmark_root, checker_binary = resolve_paths()
    if not os.path.isfile(checker_binary):
        print(f"ERROR: checker binary not found at {checker_binary}")
        print("       run `make` at the repo root to build it.")
        sys.exit(1)
    level = get_level(args.level, benchmark_root, checker_binary)

    # results/<level>/<backend>/<ts>/  (level first, then agent)
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        if os.path.isdir("/result"):
            output_dir = os.path.join("/result", level.name, backend.name, timestamp)
        else:
            output_dir = os.path.join(REPO_ROOT, "results", level.name, backend.name, timestamp)
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    print(f"Backend: {backend.name}" + (f" (model={args.model})" if args.model else ""))
    print(f"Level:   {level.name} — {level.description}")
    print(f"Output:  {output_dir}")

    # Quota gate: only meaningful for claude_code on a Claude Max subscription.
    # For other backends, or when usage.sh / OAuth creds are absent, it stays
    # disabled and never blocks a run.
    usage_script = None
    if backend.name == "claude_code" and (args.quota_5h > 0 or args.quota_7d > 0):
        candidate = args.usage_script or os.path.join(REPO_ROOT, "scripts", "usage.sh")
        if os.path.isfile(candidate):
            usage = fetch_usage(candidate)
            if usage is not None:
                usage_script = candidate
                u5 = (usage.get("five_hour") or {}).get("utilization", 0)
                u7 = (usage.get("seven_day") or {}).get("utilization", 0)
                print(
                    f"Quota:   gate ON — now 5h={u5}% (limit {args.quota_5h}%), "
                    f"7d={u7}% (limit {args.quota_7d}%), max-waits={args.quota_max_waits}"
                )
            else:
                print(
                    "Quota:   gate OFF — usage endpoint unavailable "
                    "(API-key auth or no OAuth token at ~/.claude/.credentials.json)"
                )
        elif args.usage_script:
            print(f"Quota:   gate OFF — usage script not found at {candidate}")

    benchmark_files = level.get_benchmark_files(args.filter)
    print(f"Found {len(benchmark_files)} benchmarks")

    # Resume: reuse --output-dir, skip benchmarks already recorded PASS there,
    # and seed `results` so the summary stays cumulative across the rerun.
    results = []
    done_pass = set()
    if args.resume:
        prev_json = os.path.join(output_dir, "results.json")
        if os.path.isfile(prev_json):
            with open(prev_json) as f:
                results = json.load(f)
            # Skip both PASS (already done) and SKIP (operator-marked frontier
            # benchmarks deliberately excluded from retry, e.g. theorems known
            # to time out for reasons outside the agent's control).
            done_pass = {r["benchmark"] for r in results if r.get("check_verdict") in ("PASS", "SKIP")}
            n_pass = sum(1 for r in results if r.get("check_verdict") == "PASS")
            n_skip = len(done_pass) - n_pass
            print(f"Resume: loaded {len(results)} prior results, skipping {n_pass} PASS + {n_skip} SKIP")
        else:
            print(f"Resume: no prior results.json in {output_dir} — running all")

    work_items = []
    for bf in benchmark_files:
        rel = os.path.relpath(bf, level.benchmark_dir())
        if rel in done_pass:
            continue
        work_items.append(
            WorkItem(
                benchmark_path=bf,
                output_dir=output_dir,
                timeout=args.timeout,
                check_timeout=args.check_timeout,
                backend=backend,
                level=level,
                tlapm_path=tlapm_root,
                tlapm_lib=tlapm_lib,
                usage_script=usage_script,
                quota_5h=args.quota_5h,
                quota_7d=args.quota_7d,
                quota_max_waits=args.quota_max_waits,
                min_free_gb=args.min_free_gb,
            )
        )

    start_time = time.time()
    icons = {"PASS": "✅", "FAIL": "❌", "CHEATING": "⚠️", "TIMEOUT": "⏱️", "ERROR": "💥"}
    total_benchmarks = len(benchmark_files)
    prior_done = len(results)
    if args.resume:
        print(f"Resume: {len(work_items)} benchmarks left to run")

    if args.jobs == 1:
        for i, item in enumerate(work_items):
            r = run_single_benchmark(item)
            results.append(r)
            icon = icons.get(r["check_verdict"], "❓")
            tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
            print(
                f"[{prior_done + i + 1}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)"
            )
            update_summary(results, output_dir, total_benchmarks, backend.name, level.name)
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(run_single_benchmark, item): item for item in work_items}
            for done_count, future in enumerate(as_completed(futures), start=1):
                r = future.result()
                results.append(r)
                icon = icons.get(r["check_verdict"], "❓")
                tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
                print(
                    f"[{prior_done + done_count}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)"
                )
                update_summary(results, output_dir, total_benchmarks, backend.name, level.name)

    total_time = time.time() - start_time

    update_summary(results, output_dir, total_benchmarks, backend.name, level.name)
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
            print(f"  {icons.get(v, '❓')} {v}: {verdicts[v]}")
    total_in = sum(r.get("input_tokens", 0) for r in results)
    total_out = sum(r.get("output_tokens", 0) for r in results)
    print(f"  Total tokens: {total_in:,} input / {total_out:,} output")


if __name__ == "__main__":
    main()
