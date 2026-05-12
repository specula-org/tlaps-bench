#!/usr/bin/env python3
"""
Check a single TLAPS benchmark proof for correctness and cheating.

Designed for AI agents to get quick feedback during proof writing.

Usage:
    python3 check_proof.py benchmark/Euclid/GCD_GCD3.tla [--tlapm PATH] [--tlapm-lib PATH] [--timeout SECS]

Output:
    - Raw tlapm output (preserved verbatim)
    - Cheating check (compares against main branch)
    - Summary verdict: PASS / FAIL / CHEATING

Exit codes:
    0 = PASS
    1 = FAIL (proof doesn't verify)
    2 = CHEATING (tampering detected)
    3 = ERROR (could not run check)
"""

import os
import sys
import re
import shutil
import subprocess
import tempfile
import argparse
import glob


def find_tlapm():
    """Find tlapm binary."""
    for candidate in ['/tmp/tlapm15/bin/tlapm', '/tmp/tlapm/bin/tlapm', shutil.which('tlapm')]:
        if candidate and os.path.isfile(candidate):
            return candidate
    return None


def find_tlapm_lib(tlapm_path):
    """Derive lib path from tlapm binary path."""
    base = os.path.dirname(os.path.dirname(tlapm_path))
    for sub in ['lib/tlaps', 'lib/tlapm', 'lib']:
        path = os.path.join(base, sub)
        if os.path.isdir(path):
            return path
    return None


def get_main_version(filepath):
    """Get the file content from the main/master branch."""
    repo_root = subprocess.run(
        ['git', 'rev-parse', '--show-toplevel'],
        capture_output=True, text=True, cwd=os.path.dirname(filepath) or '.'
    ).stdout.strip()

    if not repo_root:
        return None

    rel_path = os.path.relpath(filepath, repo_root)

    for branch in ['main', 'master']:
        result = subprocess.run(
            ['git', 'show', f'{branch}:{rel_path}'],
            capture_output=True, text=True, cwd=repo_root
        )
        if result.returncode == 0:
            return result.stdout

    return None


def find_proof_obvious_line(lines):
    """Find the line number (0-indexed) of 'PROOF OBVIOUS' in the file."""
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == 'PROOF OBVIOUS':
            return i
    return None


def check_cheating(filepath):
    """Check for cheating by comparing against main branch.

    Returns list of (line_number_1indexed, description) issues.
    """
    issues = []

    # Get main branch version
    main_content = get_main_version(filepath)
    if main_content is None:
        issues.append((0, "WARNING: Could not retrieve main branch version for comparison"))
        return issues

    main_lines = main_content.split('\n')
    with open(filepath, 'r') as f:
        current_lines = f.read().split('\n')

    # Find PROOF OBVIOUS in main version - this is the boundary
    po_line = find_proof_obvious_line(main_lines)
    if po_line is None:
        issues.append((0, "WARNING: No PROOF OBVIOUS found in main branch version"))
        return issues

    # Everything BEFORE the PROOF OBVIOUS line must be identical
    # (the preamble: module header, definitions, preceding theorems with PROOF OMITTED)
    preamble_end = po_line  # exclusive

    for i in range(preamble_end):
        if i >= len(current_lines):
            issues.append((i + 1, f"Line deleted from preamble (was: {main_lines[i].rstrip()})"))
            continue
        if main_lines[i] != current_lines[i]:
            issues.append((i + 1, f"Preamble modified: was [{main_lines[i].rstrip()}], now [{current_lines[i].rstrip()}]"))

    if len(current_lines) < preamble_end:
        issues.append((len(current_lines), f"File truncated: preamble had {preamble_end} lines, file has {len(current_lines)}"))
        return issues

    # The proof section: from PROOF OBVIOUS line onwards (until ====)
    # Check for cheating patterns in the proof section
    proof_section = '\n'.join(current_lines[po_line:])

    # Remove comments for analysis
    clean_proof = re.sub(r'\(\*.*?\*\)', '', proof_section, flags=re.DOTALL)

    # Check for PROOF OMITTED in the proof
    for j, line in enumerate(current_lines[po_line:]):
        line_num = po_line + j + 1
        stripped = line.strip()

        # Still has PROOF OBVIOUS = hasn't attempted the proof
        if stripped == 'PROOF OBVIOUS':
            continue  # Not cheating, just unchanged

        # Strip TLA+ line comments (\*...) for analysis
        line_no_comment = re.sub(r'\\\*.*$', '', stripped).strip()

        if re.match(r'^PROOF\s+OMITTED\b', line_no_comment):
            issues.append((line_num, "PROOF OMITTED used — skips proof obligation"))

        # Check for bare OMITTED (possibly followed by comment)
        if line_no_comment == 'OMITTED':
            # Also verify it's not inside a block comment (* ... *)
            prefix = '\n'.join(current_lines[po_line:po_line + j + 1])
            clean_prefix = re.sub(r'\(\*.*?\*\)', '', prefix, flags=re.DOTALL)
            clean_last = re.sub(r'\\\*.*$', '', clean_prefix.split('\n')[-1]).strip()
            if clean_last == 'OMITTED':
                issues.append((line_num, "Bare OMITTED used as proof step"))

    # Check for new AXIOM/ASSUME declarations in proof section
    for j, line in enumerate(current_lines[po_line:]):
        line_num = po_line + j + 1
        if re.match(r'^(AXIOM|ASSUME|ASSUMPTION)\b', line.strip()):
            issues.append((line_num, f"New {line.strip().split()[0]} declaration in proof section"))

    # Check that dependency files (other .tla files in same dir) are unmodified
    bench_dir = os.path.dirname(filepath)
    repo_root = subprocess.run(
        ['git', 'rev-parse', '--show-toplevel'],
        capture_output=True, text=True, cwd=bench_dir or '.'
    ).stdout.strip()

    if repo_root:
        for dep_file in glob.glob(os.path.join(bench_dir, '*.tla')):
            if os.path.abspath(dep_file) == os.path.abspath(filepath):
                continue
            dep_basename = os.path.basename(dep_file)
            dep_rel = os.path.relpath(dep_file, repo_root)
            # Get main branch version of this dependency
            dep_main = None
            for branch in ['main', 'master']:
                r = subprocess.run(
                    ['git', 'show', f'{branch}:{dep_rel}'],
                    capture_output=True, text=True, cwd=repo_root
                )
                if r.returncode == 0:
                    dep_main = r.stdout
                    break
            if dep_main is None:
                continue  # dependency wasn't in initial commit, skip
            with open(dep_file, 'r') as f:
                dep_current = f.read()
            if dep_current != dep_main:
                issues.append((0, f"Dependency file {dep_basename} was modified — not allowed"))

    return issues


def main():
    parser = argparse.ArgumentParser(description='Check a single TLAPS benchmark proof')
    parser.add_argument('file', help='Path to the benchmark .tla file')
    parser.add_argument('--tlapm', default=None, help='Path to tlapm binary')
    parser.add_argument('--tlapm-lib', default=None, help='Path to tlapm lib directory')
    parser.add_argument('--timeout', type=int, default=120, help='Timeout in seconds')
    parser.add_argument('--output', '-o', default=None, help='Write results to this file (default: <input>.result)')
    args = parser.parse_args()

    filepath = os.path.abspath(args.file)
    if not os.path.isfile(filepath):
        print(f"ERROR: File not found: {filepath}")
        sys.exit(3)

    # Set up output: write to file and stdout
    output_path = args.output
    if output_path is None:
        output_path = os.path.splitext(filepath)[0] + '.result'

    # Collect all output lines, print at end and write to file
    output_lines = []

    def emit(line=""):
        output_lines.append(line)
        print(line)

    # Find tlapm
    tlapm_path = args.tlapm or find_tlapm()
    if not tlapm_path:
        emit("ERROR: tlapm not found. Use --tlapm to specify path.")
        with open(output_path, 'w') as f:
            f.write('\n'.join(output_lines) + '\n')
        sys.exit(3)

    tlapm_lib = args.tlapm_lib or find_tlapm_lib(tlapm_path)
    if not tlapm_lib:
        emit("ERROR: tlapm lib not found. Use --tlapm-lib to specify path.")
        with open(output_path, 'w') as f:
            f.write('\n'.join(output_lines) + '\n')
        sys.exit(3)

    emit(f"Checking: {os.path.relpath(filepath)}")
    emit(f"tlapm: {tlapm_path}")
    emit()

    # --- Step 1: Run tlapm ---
    emit("=" * 60)
    emit("TLAPM OUTPUT")
    emit("=" * 60)

    tmp_dir = tempfile.mkdtemp(prefix='tlaps_check_')
    try:
        basename = os.path.basename(filepath)
        tmp_file = os.path.join(tmp_dir, basename)
        shutil.copy2(filepath, tmp_file)

        # Copy dependency files from the same directory
        bench_dir = os.path.dirname(filepath)
        for dep_file in glob.glob(os.path.join(bench_dir, '*.tla')):
            dep_basename = os.path.basename(dep_file)
            if dep_basename != basename:
                shutil.copy2(dep_file, os.path.join(tmp_dir, dep_basename))

        cmd = [tlapm_path, '-I', tlapm_lib, tmp_file]
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=args.timeout,
                cwd=tmp_dir
            )
            tlapm_output = result.stdout + result.stderr
            tlapm_exit = result.returncode
        except subprocess.TimeoutExpired:
            tlapm_output = f"TIMEOUT after {args.timeout}s"
            tlapm_exit = -1
        except Exception as e:
            tlapm_output = f"ERROR: {e}"
            tlapm_exit = -2

        for line in tlapm_output.split('\n'):
            emit(line)
        tlapm_passed = (tlapm_exit == 0)
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)

    # --- Step 2: Cheating check ---
    emit()
    emit("=" * 60)
    emit("CHEATING CHECK")
    emit("=" * 60)

    cheating_issues = check_cheating(filepath)
    real_issues = [i for i in cheating_issues if not i[1].startswith("WARNING:")]
    warnings = [i for i in cheating_issues if i[1].startswith("WARNING:")]

    for line_num, desc in warnings:
        emit(f"  WARNING: {desc}")

    if real_issues:
        for line_num, desc in real_issues:
            emit(f"  Line {line_num}: {desc}")
    else:
        emit("  No cheating detected.")

    # --- Step 3: Verdict ---
    emit()
    emit("=" * 60)
    emit("VERDICT")
    emit("=" * 60)

    if real_issues:
        verdict = "CHEATING"
        exit_code = 2
        emit(f"  ⚠️  CHEATING — {len(real_issues)} issue(s) found")
    elif tlapm_passed:
        verdict = "PASS"
        exit_code = 0
        emit(f"  ✅ PASS — all obligations proved")
    else:
        verdict = "FAIL"
        exit_code = 1
        # Extract obligation summary
        m = re.search(r'(\d+)/(\d+) obligation', tlapm_output)
        if m:
            emit(f"  ❌ FAIL — {m.group(1)}/{m.group(2)} obligations failed")
        elif "TIMEOUT" in tlapm_output:
            emit(f"  ❌ FAIL — timeout after {args.timeout}s")
        else:
            emit(f"  ❌ FAIL — tlapm exit code {tlapm_exit}")

    # Write result file
    with open(output_path, 'w') as f:
        f.write('\n'.join(output_lines) + '\n')
    emit(f"\nResult written to: {output_path}")

    sys.exit(exit_code)


if __name__ == '__main__':
    main()
