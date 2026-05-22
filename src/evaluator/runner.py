#!/usr/bin/env python3
"""
Run an agent CLI on TLAPS benchmarks to attempt automated proof writing.

For each benchmark:
1. Creates an isolated workspace (fresh git repo with only benchmark files)
2. Runs the chosen backend (codex / claude_code) with a proof-writing prompt
3. Validates the result with the level's checker
4. Saves all outputs

Usage:
    python3 runner.py [--backend codex|claude_code] [--level level1|level2] \\
                      [--model NAME] [--jobs N] [--filter PATTERN] \\
                      [--timeout SECS] [--check-timeout SECS] [--output-dir DIR]
"""

import os
import sys
import re
import glob
import json
import shlex
import shutil
import signal
import subprocess
import argparse
import tempfile
import time
import threading
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from typing import Optional

# Allow `python3 src/evaluator/runner.py` as well as module import.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from backends import get_backend, list_backends  # noqa: E402
from levels import get_level, list_levels  # noqa: E402

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# File at <repo>/src/evaluator/runner.py — ascend two levels for repo root.
REPO_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, '..', '..'))


def resolve_paths():
    """Return (benchmark_root, checker_binary) based on environment.

    Docker: /benchmark + /usr/local/bin/check_proof_bin (set by docker-compose).
    Host:   <repo>/benchmark + <repo>/check_proof_bin.
    """
    if os.path.isdir('/benchmark'):
        return '/benchmark', '/usr/local/bin/check_proof_bin'
    return os.path.join(REPO_ROOT, 'benchmark'), os.path.join(REPO_ROOT, 'check_proof_bin')


# Persistent tlapm location — /opt/tlapm in docker, ~/.tlapm on host.
TLAPM_PERSISTENT = '/opt/tlapm' if os.path.isdir('/opt/tlapm') else os.path.expanduser('~/.tlapm')
TLAPM_SOURCE = '/tmp/tlapm'


def ensure_tlapm():
    """Ensure tlapm is available at TLAPM_PERSISTENT (host-only fallback)."""
    if os.path.isfile(os.path.join(TLAPM_PERSISTENT, 'bin', 'tlapm')):
        print(f"tlapm at {TLAPM_PERSISTENT}")
        return
    if not os.path.isdir(TLAPM_SOURCE):
        print(f"ERROR: tlapm not found at {TLAPM_PERSISTENT} or {TLAPM_SOURCE}")
        sys.exit(1)
    print(f"Copying tlapm to {TLAPM_PERSISTENT}...")
    shutil.copytree(TLAPM_SOURCE, TLAPM_PERSISTENT)
    print("Done.")


def find_tlapm_lib(tlapm_path: str) -> Optional[str]:
    """Derive lib path from tlapm binary path. Supports 1.5 and 1.6 layouts."""
    base = os.path.dirname(os.path.dirname(tlapm_path))
    for sub in ['lib/tlapm/stdlib', 'lib/tlaps', 'lib/tlapm', 'lib']:
        path = os.path.join(base, sub)
        if os.path.isdir(path):
            return path
    return None


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


def update_summary(results, output_dir, total_benchmarks, backend_name, level_name):
    """Incrementally update summary.md + results.json with current results."""
    with _summary_lock:
        total = len(results)
        verdicts = {}
        for r in results:
            v = r['check_verdict']
            verdicts[v] = verdicts.get(v, 0) + 1

        total_input = sum(r.get('input_tokens', 0) for r in results)
        total_output = sum(r.get('output_tokens', 0) for r in results)

        lines = []
        lines.append(f"# {backend_name} on {level_name}\n")
        lines.append(f"**Date**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**Progress**: {total}/{total_benchmarks}")
        lines.append(f"**Total tokens**: {total_input:,} input / {total_output:,} output\n")

        lines.append("## Summary\n")
        lines.append("| Verdict | Count |")
        lines.append("|---------|-------|")
        for v in ['PASS', 'FAIL', 'CHEATING', 'TIMEOUT', 'ERROR']:
            count = verdicts.get(v, 0)
            if count > 0:
                icon = {'PASS': '✅', 'FAIL': '❌', 'CHEATING': '⚠️', 'TIMEOUT': '⏱️', 'ERROR': '💥'}[v]
                lines.append(f"| {icon} {v} | {count} |")
        lines.append("")

        lines.append("## Details\n")
        lines.append("| Benchmark | Verdict | Time | Obligations | Tokens (in/out) | Notes |")
        lines.append("|-----------|---------|------|-------------|-----------------|-------|")
        for r in sorted(results, key=lambda x: x['benchmark']):
            icon = {'PASS': '✅', 'FAIL': '❌', 'CHEATING': '⚠️', 'TIMEOUT': '⏱️', 'ERROR': '💥'}.get(r['check_verdict'], '❓')
            notes = r.get('error', '')
            tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
            if 'obligations' in r:
                obs = str(r['obligations'])
            elif 'obligations_failed' in r:
                obs = f"{r['obligations_failed']}/{r['obligations_total']} failed"
            else:
                obs = ''
            lines.append(f"| `{r['benchmark']}` | {icon} {r['check_verdict']} | {r['time_secs']:.0f}s | {obs} | {tokens} | {notes} |")
        lines.append("")

        report = '\n'.join(lines)
        report_path = os.path.join(output_dir, 'summary.md')
        with open(report_path, 'w') as f:
            f.write(report)

        with open(os.path.join(output_dir, 'results.json'), 'w') as f:
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
        'benchmark': rel_path,
        'module': module_dir,
        'theorem': name_no_ext,
        'backend': backend.name,
        'level': level.name,
        'agent_exit': -1,
        'check_verdict': 'ERROR',
        'time_secs': 0,
        'error': '',
    }

    workspace = tempfile.mkdtemp(prefix=f'{backend.name}_bench_{name_no_ext}_')
    try:
        # Copy benchmark + dependencies into the isolated workspace
        shutil.copy2(item.benchmark_path, os.path.join(workspace, basename))
        for dep in level.get_dependencies(item.benchmark_path):
            shutil.copy2(dep, os.path.join(workspace, os.path.basename(dep)))

        # Init git repo with original files as initial commit (the baseline
        # the cheating check compares against)
        subprocess.run(['git', 'init'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'add', '.'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'commit', '-m', 'initial benchmark'],
                       capture_output=True, cwd=workspace,
                       env={**os.environ, 'GIT_AUTHOR_NAME': 'bench',
                            'GIT_AUTHOR_EMAIL': 'bench@bench',
                            'GIT_COMMITTER_NAME': 'bench',
                            'GIT_COMMITTER_EMAIL': 'bench@bench'})

        # Copy checker binary AFTER the initial commit so it's not in the baseline
        checker_bin = level.checker_binary_path()
        check_bin_name = os.path.basename(checker_bin)
        check_bin_dest = os.path.join(workspace, check_bin_name)
        shutil.copy2(checker_bin, check_bin_dest)
        os.chmod(check_bin_dest, 0o755)

        # Archive the original benchmark
        shutil.copy2(item.benchmark_path, os.path.join(result_dir, 'benchmark.tla'))

        # Build prompt
        prompt = level.build_prompt(basename, item.tlapm_path, item.tlapm_lib)
        prompt_file = os.path.join(result_dir, 'prompt.txt')
        with open(prompt_file, 'w') as f:
            f.write(prompt)

        # Run the agent
        agent_jsonl = os.path.join(result_dir, f'{backend.name}_output.jsonl')
        cmd = backend.build_command(workspace, result_dir)

        # Source shell profile for host env vars (no-op in docker).
        shell_cmd = 'source ~/.zshrc 2>/dev/null; source ~/.bashrc 2>/dev/null; exec ' + ' '.join(
            shlex.quote(c) for c in cmd
        )

        start_time = time.time()
        try:
            with open(agent_jsonl, 'w') as jsonl_f:
                proc = subprocess.Popen(
                    ['bash', '-c', shell_cmd],
                    stdin=subprocess.PIPE,
                    stdout=jsonl_f,
                    stderr=subprocess.PIPE,
                    text=True,
                    cwd=workspace,
                    start_new_session=True,  # own process group for clean kill
                )
                try:
                    _, stderr = proc.communicate(input=prompt, timeout=item.timeout)
                except subprocess.TimeoutExpired:
                    # Kill entire process group (agent + tlapm + z3 + isabelle)
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    raise
            result['agent_exit'] = proc.returncode
            if stderr:
                with open(os.path.join(result_dir, 'agent_stderr.txt'), 'w') as f:
                    f.write(stderr)
        except subprocess.TimeoutExpired:
            result['agent_exit'] = -1
            result['error'] = f'{backend.name} timeout after {item.timeout}s'
        except Exception as e:
            result['agent_exit'] = -2
            result['error'] = str(e)

        elapsed = time.time() - start_time
        result['time_secs'] = elapsed

        transcript, input_tokens, output_tokens = backend.parse_output(agent_jsonl)
        result['input_tokens'] = input_tokens
        result['output_tokens'] = output_tokens

        transcript_path = os.path.join(result_dir, 'transcript.txt')
        with open(transcript_path, 'w') as f:
            f.write(f"Benchmark: {rel_path}\n")
            f.write(f"Time: {elapsed:.0f}s\n")
            f.write(f"Tokens: {input_tokens:,} input / {output_tokens:,} output\n")
            f.write("=" * 60 + "\n\n")
            f.write(transcript)

        # Copy all .tla files from workspace (solution + dependencies)
        solution_path = os.path.join(workspace, basename)
        for tla_file in glob.glob(os.path.join(workspace, '*.tla')):
            shutil.copy2(tla_file, os.path.join(result_dir, os.path.basename(tla_file)))
        if os.path.isfile(solution_path):
            shutil.copy2(solution_path, os.path.join(result_dir, 'solution.tla'))

        # Copy .result file if the agent ran the checker itself
        result_file = os.path.join(workspace, name_no_ext + '.result')
        if os.path.isfile(result_file):
            shutil.copy2(result_file, os.path.join(result_dir, 'agent_check.result'))

        # Run our own checker via the level
        check_result_path = os.path.join(result_dir, 'check.result')
        cmd = level.checker_command(workspace, basename, check_result_path, item.check_timeout)
        try:
            check_proc = subprocess.run(
                cmd,
                capture_output=True, text=True, timeout=item.check_timeout + 60,
                cwd=workspace,
            )
            check_log = os.path.join(result_dir, 'check_debug.txt')
            with open(check_log, 'w') as dbg:
                dbg.write(f"exit code: {check_proc.returncode}\n")
                dbg.write(f"stdout:\n{check_proc.stdout}\n")
                dbg.write(f"stderr:\n{check_proc.stderr}\n")
            if check_proc.returncode == 0:
                result['check_verdict'] = 'PASS'
            elif check_proc.returncode == 2:
                result['check_verdict'] = 'CHEATING'
            elif check_proc.returncode == 1:
                result['check_verdict'] = 'FAIL'
            else:
                result['check_verdict'] = 'ERROR'
            ob_matches = re.findall(r'All (\d+) obligation', check_proc.stdout)
            if ob_matches:
                result['obligations'] = int(ob_matches[-1])
            else:
                fail_match = re.search(r'(\d+)/(\d+) obligation', check_proc.stdout)
                if fail_match:
                    result['obligations_failed'] = int(fail_match.group(1))
                    result['obligations_total'] = int(fail_match.group(2))
        except subprocess.TimeoutExpired:
            result['check_verdict'] = 'TIMEOUT'
        except Exception as e:
            result['check_verdict'] = 'ERROR'
            result['error'] = str(e)

    finally:
        shutil.rmtree(workspace, ignore_errors=True)

    return result


def main():
    parser = argparse.ArgumentParser(description='Run an agent CLI on TLAPS benchmarks')
    parser.add_argument('--backend', default='codex', choices=list_backends(),
                        help='Agent backend (default: codex)')
    parser.add_argument('--level', default='level1', choices=list_levels(),
                        help='Benchmark level (default: level1)')
    parser.add_argument('--model', default=None,
                        help='Override the backend default model')
    parser.add_argument('--jobs', type=int, default=1, help='Parallel agent runs')
    parser.add_argument('--filter', default=None, help='Only run benchmarks matching pattern')
    parser.add_argument('--timeout', type=int, default=7200,
                        help='Agent timeout per benchmark in seconds (default: 7200)')
    parser.add_argument('--check-timeout', type=int, default=120,
                        help='Checker timeout per benchmark in seconds (default: 120)')
    parser.add_argument('--output-dir', default=None, help='Output directory')
    args = parser.parse_args()

    backend = get_backend(args.backend, model=args.model)

    missing_env = [v for v in backend.required_env() if not os.environ.get(v)]
    if missing_env:
        print(f"ERROR: {backend.name} backend requires env vars: {', '.join(missing_env)}")
        sys.exit(1)

    ensure_tlapm()
    tlapm_path = os.path.join(TLAPM_PERSISTENT, 'bin', 'tlapm')
    tlapm_lib = find_tlapm_lib(tlapm_path)
    if not tlapm_lib:
        print(f"ERROR: tlapm lib not found near {tlapm_path}")
        sys.exit(1)

    benchmark_root, checker_binary = resolve_paths()
    if not os.path.isfile(checker_binary):
        print(f"ERROR: checker binary not found at {checker_binary}")
        print(f"       run `make` at the repo root to build it.")
        sys.exit(1)
    level = get_level(args.level, benchmark_root, checker_binary)

    # results/<backend>/<level>/<ts>/
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = time.strftime('%Y%m%d_%H%M%S')
        if os.path.isdir('/result'):
            output_dir = os.path.join('/result', backend.name, level.name, timestamp)
        else:
            output_dir = os.path.join(SCRIPT_DIR, 'results', backend.name, level.name, timestamp)
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    print(f"Backend: {backend.name}" + (f" (model={args.model})" if args.model else ""))
    print(f"Level:   {level.name} — {level.description}")
    print(f"Output:  {output_dir}")

    benchmark_files = level.get_benchmark_files(args.filter)
    print(f"Found {len(benchmark_files)} benchmarks")

    work_items = [
        WorkItem(
            benchmark_path=bf,
            output_dir=output_dir,
            timeout=args.timeout,
            check_timeout=args.check_timeout,
            backend=backend,
            level=level,
            tlapm_path=tlapm_path,
            tlapm_lib=tlapm_lib,
        )
        for bf in benchmark_files
    ]

    results = []
    start_time = time.time()
    icons = {'PASS': '✅', 'FAIL': '❌', 'CHEATING': '⚠️', 'TIMEOUT': '⏱️', 'ERROR': '💥'}
    total_benchmarks = len(work_items)

    if args.jobs == 1:
        for i, item in enumerate(work_items):
            r = run_single_benchmark(item)
            results.append(r)
            icon = icons.get(r['check_verdict'], '❓')
            tokens = f"{r.get('input_tokens',0):,}/{r.get('output_tokens',0):,}"
            print(f"[{i+1}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)")
            update_summary(results, output_dir, total_benchmarks, backend.name, level.name)
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(run_single_benchmark, item): item for item in work_items}
            done_count = 0
            for future in as_completed(futures):
                done_count += 1
                r = future.result()
                results.append(r)
                icon = icons.get(r['check_verdict'], '❓')
                tokens = f"{r.get('input_tokens',0):,}/{r.get('output_tokens',0):,}"
                print(f"[{done_count}/{total_benchmarks}] {icon} {r['benchmark']} ({r['time_secs']:.0f}s, {tokens} tok)")
                update_summary(results, output_dir, total_benchmarks, backend.name, level.name)

    total_time = time.time() - start_time

    update_summary(results, output_dir, total_benchmarks, backend.name, level.name)
    report_path = os.path.join(output_dir, 'summary.md')

    print(f"\n{'='*60}")
    print(f"Completed in {total_time:.0f}s")
    print(f"Report: {report_path}")

    verdicts = {}
    for r in results:
        v = r['check_verdict']
        verdicts[v] = verdicts.get(v, 0) + 1
    for v in ['PASS', 'FAIL', 'CHEATING', 'TIMEOUT', 'ERROR']:
        if v in verdicts:
            print(f"  {icons.get(v, '❓')} {v}: {verdicts[v]}")
    total_in = sum(r.get('input_tokens', 0) for r in results)
    total_out = sum(r.get('output_tokens', 0) for r in results)
    print(f"  Total tokens: {total_in:,} input / {total_out:,} output")


if __name__ == '__main__':
    main()
