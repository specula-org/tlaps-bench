#!/usr/bin/env python3
"""
Run an agent CLI on TLAPS benchmarks to attempt automated proof writing.

For each benchmark:
1. Creates an isolated workspace (fresh git repo with only benchmark files)
2. Runs the chosen backend (codex / claude_code) with a proof-writing prompt
3. Validates the result with check_proof (binary)
4. Saves all outputs

Usage:
    python3 runner.py [--backend codex|claude_code] [--jobs N] [--filter PATTERN] [--timeout SECS] [--output-dir DIR]
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

# Allow `python3 src/evaluator/runner.py` as well as module import.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from backends import get_backend, list_backends

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# File now at <repo>/src/evaluator/runner.py — ascend two levels for the repo root.
REPO_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, '..', '..'))

# In Docker: benchmark at /benchmark, scripts at /scripts (set in docker-compose).
# On host: default to benchmark/level1 under the repo root.
if os.path.isdir('/benchmark'):
    BENCHMARK_DIR = '/benchmark'
    CHECK_PROOF_SCRIPT = '/scripts/check_proof_bin'
else:
    BENCHMARK_DIR = os.path.join(REPO_ROOT, 'benchmark', 'level1')
    CHECK_PROOF_SCRIPT = os.path.join(REPO_ROOT, 'check_proof_bin')

# Persistent tlapm location — use /opt/tlapm in docker, ~/.tlapm on host
TLAPM_PERSISTENT = '/opt/tlapm' if os.path.isdir('/opt/tlapm') else os.path.expanduser('~/.tlapm')
TLAPM_SOURCE = '/tmp/tlapm'


def ensure_tlapm():
    """Ensure tlapm is available."""
    if os.path.isfile(os.path.join(TLAPM_PERSISTENT, 'bin', 'tlapm')):
        print(f"tlapm at {TLAPM_PERSISTENT}")
        return
    # Try copying from /tmp/tlapm (host-only fallback)
    if not os.path.isdir(TLAPM_SOURCE):
        print(f"ERROR: tlapm not found at {TLAPM_PERSISTENT} or {TLAPM_SOURCE}")
        sys.exit(1)
    print(f"Copying tlapm to {TLAPM_PERSISTENT}...")
    shutil.copytree(TLAPM_SOURCE, TLAPM_PERSISTENT)
    print("Done.")


def get_benchmark_files(filter_pattern=None):
    """Get list of benchmark .tla files (those with underscore in name)."""
    files = sorted(glob.glob(os.path.join(BENCHMARK_DIR, '**', '*.tla'), recursive=True))
    files = [f for f in files if '_' in os.path.splitext(os.path.basename(f))[0]]
    if filter_pattern:
        patterns = filter_pattern.split(',')
        files = [f for f in files if any(p.strip() in f for p in patterns)]
    return files


def get_dependency_files(benchmark_path):
    """Get dependency .tla files from the same directory (no underscore in name)."""
    bench_dir = os.path.dirname(benchmark_path)
    deps = []
    for f in glob.glob(os.path.join(bench_dir, '*.tla')):
        bn = os.path.splitext(os.path.basename(f))[0]
        if '_' not in bn:
            deps.append(f)
    return deps


# Lock for thread-safe summary updates
_summary_lock = threading.Lock()


def update_summary(results, output_dir, total_benchmarks):
    """Incrementally update summary.md with current results."""
    with _summary_lock:
        total = len(results)
        verdicts = {}
        for r in results:
            v = r['check_verdict']
            verdicts[v] = verdicts.get(v, 0) + 1

        total_input = sum(r.get('input_tokens', 0) for r in results)
        total_output = sum(r.get('output_tokens', 0) for r in results)

        lines = []
        lines.append("# Codex Benchmark Results\n")
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


_PROMPT_DIR = os.path.join(SCRIPT_DIR, 'prompts')


def build_prompt(benchmark_basename, level='level1'):
    """Build the proof-writing prompt by loading the template for the given level."""
    template_path = os.path.join(_PROMPT_DIR, f'{level}.txt')
    with open(template_path, 'r') as f:
        template = f.read()
    return template.format(
        benchmark_basename=benchmark_basename,
        tlapm_path=TLAPM_PERSISTENT,
    )


def run_single_benchmark(args_tuple):
    """Run the agent backend on a single benchmark. Returns result dict."""
    benchmark_path, output_dir, timeout, backend = args_tuple

    rel_path = os.path.relpath(benchmark_path, BENCHMARK_DIR)
    module_dir = os.path.basename(os.path.dirname(benchmark_path))
    basename = os.path.basename(benchmark_path)
    name_no_ext = os.path.splitext(basename)[0]

    # Create output directory
    result_dir = os.path.join(output_dir, module_dir, name_no_ext)
    os.makedirs(result_dir, exist_ok=True)

    result = {
        'benchmark': rel_path,
        'module': module_dir,
        'theorem': name_no_ext,
        'backend': backend.name,
        'agent_exit': -1,
        'check_verdict': 'ERROR',
        'time_secs': 0,
        'error': '',
    }

    # Create isolated workspace
    workspace = tempfile.mkdtemp(prefix=f'codex_bench_{name_no_ext}_')
    try:
        # Copy benchmark file
        shutil.copy2(benchmark_path, os.path.join(workspace, basename))

        # Copy dependency files
        for dep in get_dependency_files(benchmark_path):
            shutil.copy2(dep, os.path.join(workspace, os.path.basename(dep)))

        # Copy check_proof binary (after initial commit so it's not in the baseline)
        # Init git repo with the original benchmark as the initial commit
        subprocess.run(['git', 'init'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'add', '.'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'commit', '-m', 'initial benchmark'],
                       capture_output=True, cwd=workspace,
                       env={**os.environ, 'GIT_AUTHOR_NAME': 'bench',
                            'GIT_AUTHOR_EMAIL': 'bench@bench',
                            'GIT_COMMITTER_NAME': 'bench',
                            'GIT_COMMITTER_EMAIL': 'bench@bench'})

        # Now copy check_proof binary (after initial commit so it's not in the baseline)
        check_bin_dest = os.path.join(workspace, 'check_proof_bin')
        shutil.copy2(CHECK_PROOF_SCRIPT, check_bin_dest)
        os.chmod(check_bin_dest, 0o755)

        # Save original benchmark to results
        shutil.copy2(benchmark_path, os.path.join(result_dir, 'benchmark.tla'))

        # Build prompt
        prompt = build_prompt(basename)

        # Save prompt to file for stdin
        prompt_file = os.path.join(result_dir, 'prompt.txt')
        with open(prompt_file, 'w') as f:
            f.write(prompt)

        # Run the agent
        agent_jsonl = os.path.join(result_dir, f'{backend.name}_output.jsonl')
        cmd = backend.build_command(workspace, result_dir)

        # Build a shell command; source shell profile for host env vars (no-op in docker)
        shell_cmd = 'source ~/.zshrc 2>/dev/null; source ~/.bashrc 2>/dev/null; exec ' + ' '.join(
            shlex.quote(c) for c in cmd
        )

        # Use bash (available in docker); fall back to zsh on host
        shell = 'bash'

        start_time = time.time()
        try:
            with open(agent_jsonl, 'w') as jsonl_f:
                proc = subprocess.Popen(
                    [shell, '-c', shell_cmd],
                    stdin=subprocess.PIPE,
                    stdout=jsonl_f,
                    stderr=subprocess.PIPE,
                    text=True,
                    cwd=workspace,
                    start_new_session=True,  # own process group for clean kill
                )
                try:
                    _, stderr = proc.communicate(input=prompt, timeout=timeout)
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
            result['error'] = f'{backend.name} timeout after {timeout}s'
        except Exception as e:
            result['agent_exit'] = -2
            result['error'] = str(e)

        elapsed = time.time() - start_time
        result['time_secs'] = elapsed

        # Parse JSONL for human-readable transcript and token usage
        transcript, input_tokens, output_tokens = backend.parse_output(agent_jsonl)
        result['input_tokens'] = input_tokens
        result['output_tokens'] = output_tokens

        # Write human-readable transcript
        transcript_path = os.path.join(result_dir, 'transcript.txt')
        with open(transcript_path, 'w') as f:
            f.write(f"Benchmark: {rel_path}\n")
            f.write(f"Time: {elapsed:.0f}s\n")
            f.write(f"Tokens: {input_tokens:,} input / {output_tokens:,} output\n")
            f.write("=" * 60 + "\n\n")
            f.write(transcript)

        # Copy all .tla files from workspace (solution + dependencies) — skip .tlacache
        solution_path = os.path.join(workspace, basename)
        for tla_file in glob.glob(os.path.join(workspace, '*.tla')):
            shutil.copy2(tla_file, os.path.join(result_dir, os.path.basename(tla_file)))
        # Also save solution.tla as a convenience alias
        if os.path.isfile(solution_path):
            shutil.copy2(solution_path, os.path.join(result_dir, 'solution.tla'))

        # Copy .result file if check_proof was run by the agent itself
        result_file = os.path.join(workspace, name_no_ext + '.result')
        if os.path.isfile(result_file):
            shutil.copy2(result_file, os.path.join(result_dir, 'agent_check.result'))

        # Run our own check_proof on the solution
        check_result_path = os.path.join(result_dir, 'check.result')
        try:
            check_proc = subprocess.run(
                [os.path.join(workspace, 'check_proof_bin'), solution_path,
                 '--output', check_result_path, '--timeout', '120'],
                capture_output=True, text=True, timeout=180,
                cwd=workspace,
            )
            # Save check output for debugging
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
            # Extract obligation count from tlapm output
            ob_matches = re.findall(r'All (\d+) obligation', check_proc.stdout)
            if ob_matches:
                result['obligations'] = int(ob_matches[-1])
            else:
                # Try failed obligation pattern: "X/Y obligations failed"
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
    parser.add_argument('--jobs', type=int, default=1, help='Parallel agent runs')
    parser.add_argument('--filter', default=None, help='Only run benchmarks matching pattern')
    parser.add_argument('--timeout', type=int, default=7200, help='Timeout per benchmark in seconds (default: 2 hours)')
    parser.add_argument('--output-dir', default=None, help='Output directory')
    args = parser.parse_args()

    backend = get_backend(args.backend)

    # Sanity-check required env vars early so we fail fast.
    missing_env = [v for v in backend.required_env() if not os.environ.get(v)]
    if missing_env:
        print(f"ERROR: {backend.name} backend requires env vars: {', '.join(missing_env)}")
        sys.exit(1)

    # Ensure tlapm is persistent
    ensure_tlapm()

    # Set up output directory: results/<backend>/<ts>/
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = time.strftime('%Y%m%d_%H%M%S')
        # In Docker, /result is mounted; on host, use results/<backend>/ relative to script
        if os.path.isdir('/result'):
            output_dir = os.path.join('/result', backend.name, timestamp)
        else:
            output_dir = os.path.join(SCRIPT_DIR, 'results', backend.name, timestamp)
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    print(f"Backend: {backend.name}")
    print(f"Output directory: {output_dir}")

    # Get benchmarks
    benchmark_files = get_benchmark_files(args.filter)
    print(f"Found {len(benchmark_files)} benchmarks")

    # Prepare work items
    work_items = [
        (bf, output_dir, args.timeout, backend)
        for bf in benchmark_files
    ]

    # Run
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
            update_summary(results, output_dir, total_benchmarks)
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
                update_summary(results, output_dir, total_benchmarks)

    total_time = time.time() - start_time

    # Final summary
    update_summary(results, output_dir, total_benchmarks)
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
