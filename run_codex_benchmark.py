#!/usr/bin/env python3
"""
Run Codex CLI on TLAPS benchmarks to attempt automated proof writing.

For each benchmark:
1. Creates an isolated workspace (fresh git repo with only benchmark files)
2. Runs codex exec with a proof-writing prompt
3. Validates the result with check_proof.py
4. Saves all outputs

Usage:
    python3 run_codex_benchmark.py [--jobs N] [--filter PATTERN] [--timeout SECS] [--output-dir DIR]
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
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BENCHMARK_DIR = os.path.join(SCRIPT_DIR, 'benchmark')
CHECK_PROOF_SCRIPT = os.path.join(SCRIPT_DIR, 'check_proof.py')

# Persistent tlapm location
TLAPM_PERSISTENT = os.path.expanduser('~/.tlapm15')
TLAPM_SOURCE = '/tmp/tlapm15'


def ensure_tlapm():
    """Copy tlapm to persistent location if not already there."""
    if os.path.isfile(os.path.join(TLAPM_PERSISTENT, 'bin', 'tlapm')):
        print(f"tlapm already at {TLAPM_PERSISTENT}")
        return
    if not os.path.isdir(TLAPM_SOURCE):
        print(f"ERROR: tlapm source not found at {TLAPM_SOURCE}")
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


def parse_codex_jsonl(jsonl_path):
    """Parse codex JSONL output into human-readable transcript and token usage."""
    transcript_lines = []
    total_input_tokens = 0
    total_output_tokens = 0

    try:
        with open(jsonl_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue

                etype = event.get('type', '')

                if etype == 'item.completed':
                    item = event.get('item', {})
                    itype = item.get('type', '')

                    if itype == 'agent_message':
                        text = item.get('text', '')
                        if text:
                            transcript_lines.append(f"[AGENT] {text}")
                            transcript_lines.append("")

                    elif itype == 'command_execution':
                        cmd = item.get('command', '')
                        output = item.get('aggregated_output', '')
                        exit_code = item.get('exit_code', '')
                        transcript_lines.append(f"[CMD] {cmd}")
                        if output:
                            if len(output) > 3000:
                                output = output[:1500] + "\n... (truncated) ...\n" + output[-1500:]
                            transcript_lines.append(output.rstrip())
                        if exit_code is not None:
                            transcript_lines.append(f"[EXIT {exit_code}]")
                        transcript_lines.append("")

                    elif itype == 'file_edit':
                        filepath = item.get('filepath', '')
                        transcript_lines.append(f"[EDIT] {filepath}")
                        transcript_lines.append("")

                elif etype == 'error':
                    msg = event.get('message', '')
                    transcript_lines.append(f"[ERROR] {msg}")
                    transcript_lines.append("")

                # Check for usage in any event
                if 'usage' in event:
                    u = event['usage']
                    total_input_tokens += u.get('input_tokens', 0)
                    total_output_tokens += u.get('output_tokens', 0)

    except FileNotFoundError:
        pass

    transcript = '\n'.join(transcript_lines)
    return transcript, total_input_tokens, total_output_tokens


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
        lines.append("| Benchmark | Verdict | Time | Tokens (in/out) | Notes |")
        lines.append("|-----------|---------|------|-----------------|-------|")
        for r in sorted(results, key=lambda x: x['benchmark']):
            icon = {'PASS': '✅', 'FAIL': '❌', 'CHEATING': '⚠️', 'TIMEOUT': '⏱️', 'ERROR': '💥'}.get(r['check_verdict'], '❓')
            notes = r.get('error', '')
            tokens = f"{r.get('input_tokens', 0):,}/{r.get('output_tokens', 0):,}"
            lines.append(f"| `{r['benchmark']}` | {icon} {r['check_verdict']} | {r['time_secs']:.0f}s | {tokens} | {notes} |")
        lines.append("")

        report = '\n'.join(lines)
        report_path = os.path.join(output_dir, 'summary.md')
        with open(report_path, 'w') as f:
            f.write(report)

        with open(os.path.join(output_dir, 'results.json'), 'w') as f:
            json.dump(results, f, indent=2)


def build_prompt(benchmark_basename):
    """Build the proof-writing prompt for codex."""
    name_no_ext = os.path.splitext(benchmark_basename)[0]
    return f"""\
The file {benchmark_basename} contains a TLA+ theorem that cannot be verified by tlapm (the TLA+ Proof System) yet. The last theorem in the file has `PROOF OBVIOUS` as a placeholder proof that will fail. Preceding theorems have `PROOF OMITTED` which means they are admitted and available as lemmas. Please replace `PROOF OBVIOUS` with a complete, valid TLAPS proof so that tlapm can successfully verify it. The tlapm standard library is at ~/.tlapm15/lib/tlaps; please feel free to check it when needed. You should KEEP editing your proof until tlapm shows there is no error. You should NOT change any module header, operator definitions, CONSTANT or VARIABLE declarations, ASSUME/ASSUMPTION declarations, or THEOREM/LEMMA statements that appear above `PROOF OBVIOUS`; you should NOT change any preceding `PROOF OMITTED` proofs. You should NEVER use `PROOF OMITTED` or bare `OMITTED` in your proof. You are also NOT allowed to introduce new top-level AXIOM, ASSUME, ASSUMPTION, CONSTANT, or VARIABLE declarations. You should NEVER weaken theorem statements or add extra hypotheses. You can run tlapm directly: `~/.tlapm15/bin/tlapm -I ~/.tlapm15/lib/tlaps {benchmark_basename}`. Before you are done, MAKE SURE to run `python3 check_proof.py {benchmark_basename}` to double check whether you have made any illegal changes to {benchmark_basename} (fix those if you did).\
"""


def run_single_benchmark(args_tuple):
    """Run codex on a single benchmark. Returns result dict."""
    benchmark_path, output_dir, timeout = args_tuple

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
        'codex_exit': -1,
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

        # Copy check_proof.py (modified to work standalone — no git comparison in isolated env)
        # We need a standalone version that skips git-based cheating check
        # Actually, we'll create a fresh git repo so check_proof.py can compare
        # Init git repo with the original benchmark as the initial commit
        subprocess.run(['git', 'init'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'add', '.'], capture_output=True, cwd=workspace)
        subprocess.run(['git', 'commit', '-m', 'initial benchmark'],
                       capture_output=True, cwd=workspace,
                       env={**os.environ, 'GIT_AUTHOR_NAME': 'bench',
                            'GIT_AUTHOR_EMAIL': 'bench@bench',
                            'GIT_COMMITTER_NAME': 'bench',
                            'GIT_COMMITTER_EMAIL': 'bench@bench'})

        # Now copy check_proof.py (after initial commit so it's not in the baseline)
        shutil.copy2(CHECK_PROOF_SCRIPT, os.path.join(workspace, 'check_proof.py'))

        # Save original benchmark to results
        shutil.copy2(benchmark_path, os.path.join(result_dir, 'benchmark.tla'))

        # Build prompt
        prompt = build_prompt(basename)

        # Save prompt to file for stdin
        prompt_file = os.path.join(result_dir, 'prompt.txt')
        with open(prompt_file, 'w') as f:
            f.write(prompt)

        # Run codex
        codex_jsonl = os.path.join(result_dir, 'codex_output.jsonl')
        codex_last_msg = os.path.join(result_dir, 'codex_last_message.txt')

        cmd = [
            'npx', 'codex', 'exec',
            '--dangerously-bypass-approvals-and-sandbox',
            '-C', workspace,
            '-m', 'gpt55',
            '--json',
            '-o', codex_last_msg,
        ]

        # Build a shell command that sources ~/.zshrc to pick up env vars
        # (e.g. AZURE_OPENAI_API_KEY) without hardcoding secrets in code
        shell_cmd = 'source ~/.zshrc 2>/dev/null; exec ' + ' '.join(
            shlex.quote(c) for c in cmd
        )

        start_time = time.time()
        try:
            with open(codex_jsonl, 'w') as jsonl_f:
                proc = subprocess.Popen(
                    ['zsh', '-c', shell_cmd],
                    stdin=subprocess.PIPE,
                    stdout=jsonl_f,
                    stderr=subprocess.PIPE,
                    text=True,
                    start_new_session=True,  # own process group for clean kill
                )
                try:
                    _, stderr = proc.communicate(input=prompt, timeout=timeout)
                except subprocess.TimeoutExpired:
                    # Kill entire process group (codex + tlapm + z3 + isabelle)
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    raise
            result['codex_exit'] = proc.returncode
            if stderr:
                with open(os.path.join(result_dir, 'codex_stderr.txt'), 'w') as f:
                    f.write(stderr)
        except subprocess.TimeoutExpired:
            result['codex_exit'] = -1
            result['error'] = f'codex timeout after {timeout}s'
        except Exception as e:
            result['codex_exit'] = -2
            result['error'] = str(e)

        elapsed = time.time() - start_time
        result['time_secs'] = elapsed

        # Parse JSONL for human-readable transcript and token usage
        transcript, input_tokens, output_tokens = parse_codex_jsonl(codex_jsonl)
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

        # Copy the (potentially modified) benchmark file as solution
        solution_path = os.path.join(workspace, basename)
        if os.path.isfile(solution_path):
            shutil.copy2(solution_path, os.path.join(result_dir, 'solution.tla'))

        # Copy .result file if check_proof.py was run by codex
        result_file = os.path.join(workspace, name_no_ext + '.result')
        if os.path.isfile(result_file):
            shutil.copy2(result_file, os.path.join(result_dir, 'codex_check.result'))

        # Run our own check_proof.py on the solution
        check_result_path = os.path.join(result_dir, 'check.result')
        try:
            check_proc = subprocess.run(
                [sys.executable, CHECK_PROOF_SCRIPT, solution_path,
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
        except subprocess.TimeoutExpired:
            result['check_verdict'] = 'TIMEOUT'
        except Exception as e:
            result['check_verdict'] = 'ERROR'
            result['error'] = str(e)

    finally:
        shutil.rmtree(workspace, ignore_errors=True)

    return result


def main():
    parser = argparse.ArgumentParser(description='Run Codex on TLAPS benchmarks')
    parser.add_argument('--jobs', type=int, default=1, help='Parallel codex runs')
    parser.add_argument('--filter', default=None, help='Only run benchmarks matching pattern')
    parser.add_argument('--timeout', type=int, default=7200, help='Timeout per benchmark in seconds (default: 2 hours)')
    parser.add_argument('--output-dir', default=None, help='Output directory')
    args = parser.parse_args()

    # Ensure tlapm is persistent
    ensure_tlapm()

    # Set up output directory
    if args.output_dir:
        output_dir = args.output_dir
    else:
        timestamp = time.strftime('%Y%m%d_%H%M%S')
        output_dir = os.path.join(SCRIPT_DIR, 'codex_results', timestamp)
    output_dir = os.path.abspath(output_dir)
    os.makedirs(output_dir, exist_ok=True)

    print(f"Output directory: {output_dir}")

    # Get benchmarks
    benchmark_files = get_benchmark_files(args.filter)
    print(f"Found {len(benchmark_files)} benchmarks")

    # Prepare work items
    work_items = [
        (bf, output_dir, args.timeout)
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
