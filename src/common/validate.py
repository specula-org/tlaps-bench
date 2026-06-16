#!/usr/bin/env python3
"""
Validate TLAPS benchmarks by porting original proofs and running tlapm.

For each benchmark file:
1. Find the corresponding original proof from source files
2. Replace PROOF OBVIOUS with the original proof
3. Run tlapm to verify
4. Detect placeholder proofs (PROOF OMITTED)
5. Generate a markdown report

Usage:
    python3 validate_benchmarks.py [--tlapm PATH] [--tlapm-lib PATH] [--timeout SECS] [--jobs N]
"""

import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, field

# Internal imports — generate.py is in ../dataset/level1, cheating_detection here.
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, "..", "dataset", "level1"))
from cheating_detection import CheatingIssue  # noqa: E402
from generate import (  # noqa: E402
    BENCHMARK_DIR,
    PROJECT_ROOT,
    SOURCE_ROOT,
    find_source_dirs,
    find_tla_files,
    get_theorem_proof_lines,
    parse_module_name,
    parse_theorems,
)


@dataclass
class ValidationResult:
    benchmark_file: str
    module: str
    theorem_name: str
    source_file: str
    # Status
    proof_found: bool = False
    proof_ported: bool = False
    tlapm_passed: bool = False
    tlapm_exit_code: int = -1
    tlapm_output: str = ""
    tlapm_time_secs: float = 0.0
    # Proof metrics
    proof_lines_count: int = 0  # non-empty, non-comment proof lines
    # Cheating
    cheating_issues: list[CheatingIssue] = field(default_factory=list)
    # Error
    error: str = ""

    @property
    def status(self) -> str:
        if self.error:
            return "ERROR"
        if not self.proof_found:
            return "NO_PROOF"
        if self.cheating_issues:
            return "OMITTED"  # source proof uses PROOF OMITTED
        if self.tlapm_passed:
            return "PASS"
        return "FAIL"


def _derive_tlapm_lib(tlapm_path: str) -> str | None:
    """Pick the stdlib dir based on tlapm install layout.

    tlapm 1.6 stores .tla files at lib/tlapm/stdlib; tlapm 1.5 at lib/tlaps.
    """
    base = os.path.dirname(os.path.dirname(tlapm_path))
    for sub in ["lib/tlapm/stdlib", "lib/tlaps", "lib/tlapm", "lib"]:
        cand = os.path.join(base, sub)
        if os.path.isdir(cand):
            return cand
    return None


def find_original_proof(
    source_files_by_module: dict, theorem_name: str, source_basename: str
) -> tuple[str, list[str], int, int] | None:
    """Find the original proof for a theorem from source files.

    Returns (source_file, proof_lines, stmt_start, proof_end) or None.
    """
    # source_basename is like "Cantor1", "Voting", etc.
    # Try to find in all source files
    for _mod_name, filepath in source_files_by_module.items():
        if os.path.splitext(os.path.basename(filepath))[0] != source_basename:
            continue

        with open(filepath) as f:
            content = f.read()
        lines = content.split("\n")
        theorems = parse_theorems(lines)

        for thm in theorems:
            if thm.name == theorem_name and thm.has_proof:
                proof_lines = lines[thm.proof_start : thm.proof_end + 1]
                return filepath, proof_lines, thm.statement_start, thm.proof_end

    return None


def count_proof_lines(proof_lines: list[str]) -> int:
    """Count non-empty, non-comment lines in proof."""
    count = 0
    in_comment = False
    for line in proof_lines:
        stripped = line.strip()
        if not stripped:
            continue
        # Handle block comments
        while stripped:
            if in_comment:
                end = stripped.find("*)")
                if end == -1:
                    break  # entire line is inside comment
                stripped = stripped[end + 2 :].strip()
                in_comment = False
            else:
                start = stripped.find("(*")
                if start == -1:
                    # No comment on this line, it's a real line
                    count += 1
                    break
                elif start > 0:
                    # Some content before comment
                    count += 1
                    stripped = stripped[start + 2 :]
                    in_comment = True
                    break
                else:
                    # Comment starts at beginning
                    stripped = stripped[2:]
                    in_comment = True
    return count


def port_proof_to_benchmark(benchmark_path: str, proof_lines: list[str]) -> str:
    """Replace PROOF OBVIOUS in the benchmark file with the original proof.

    Returns the new content.
    """
    with open(benchmark_path) as f:
        content = f.read()

    lines = content.split("\n")

    # Find the PROOF OBVIOUS line (should be the last theorem's proof)
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() == "PROOF OBVIOUS":
            # Replace this line with the original proof
            new_lines = lines[:i] + proof_lines + lines[i + 1 :]
            return "\n".join(new_lines)

    # Fallback: if no PROOF OBVIOUS found, try appending proof before ====
    for i in range(len(lines) - 1, -1, -1):
        if re.match(r"^={3,}", lines[i].strip()):
            new_lines = lines[:i] + proof_lines + [lines[i]]
            return "\n".join(new_lines)

    return content  # unchanged


def run_tlapm(tla_file: str, tlapm_path: str, tlapm_lib: str, timeout: int = 120) -> tuple[int, str, float]:
    """Run tlapm on a TLA+ file. Returns (exit_code, output, elapsed_secs)."""
    cmd = [tlapm_path, "-I", tlapm_lib]
    community_lib = os.path.join(PROJECT_ROOT, "lib", "community")
    if os.path.isdir(community_lib):
        cmd += ["-I", community_lib]
    cmd.append(tla_file)
    start = time.time()
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, cwd=os.path.dirname(tla_file) or "."
        )
        elapsed = time.time() - start
        output = result.stdout + "\n" + result.stderr
        return result.returncode, output.strip(), elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        return -1, f"TIMEOUT after {timeout}s", elapsed
    except Exception as e:
        elapsed = time.time() - start
        return -2, f"ERROR: {str(e)}", elapsed


def validate_single_benchmark(args_tuple):
    """Validate a single benchmark. Designed for ProcessPoolExecutor."""
    (benchmark_path, source_files, tlapm_path, tlapm_lib, timeout) = args_tuple

    basename = os.path.basename(benchmark_path)
    module_dir = os.path.basename(os.path.dirname(benchmark_path))
    name_no_ext = os.path.splitext(basename)[0]

    # Parse source_basename and theorem_name from filename
    # Format: SourceFile_TheoremName.tla (possibly with _N suffix for duplicates)
    # We need to try matching against known source files
    result = ValidationResult(
        benchmark_file=os.path.relpath(benchmark_path, PROJECT_ROOT),
        module=module_dir,
        theorem_name="",
        source_file="",
    )

    # Try to find the theorem by parsing the benchmark file itself
    with open(benchmark_path) as f:
        benchmark_content = f.read()

    bench_lines = benchmark_content.split("\n")
    # Find the target theorem - it's the last named THEOREM/LEMMA in the file
    target_thm_name = None
    for line in reversed(bench_lines):
        m = re.match(r"^(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", line.strip())
        if m:
            target_thm_name = m.group(2)
            break

    if not target_thm_name:
        result.error = "No theorems found in benchmark file"
        return result

    result.theorem_name = target_thm_name

    # Find which source file this came from
    # The benchmark name format is SourceBasename_TheoremName[_N].tla
    # For merged files, the theorem may come from a dependency file
    found_proof = None

    # First, try the primary source file matching the benchmark name
    # Then fall back to searching all source files in the same module directory.
    # BOTH must be scoped to the benchmark's own top-level spec dir (module_dir):
    # multiple specs can share a module basename (e.g. Consensus.tla exists in
    # tlaplus_examples_Paxos, _PaxosHowToWinATuringAward and _byzpaxos, each with
    # a THEOREM Invariance). Without this scope the matcher could port a
    # same-named proof from a *different* spec
    candidates = []
    for source_basename, src_file in source_files:
        rel = os.path.relpath(src_file, SOURCE_ROOT)
        if rel.split(os.sep)[0] != module_dir:
            continue
        src_basename_noext = os.path.splitext(os.path.basename(src_file))[0]
        if name_no_ext.startswith(src_basename_noext + "_"):
            candidates.insert(0, (source_basename, src_file))  # primary match first
        else:
            candidates.append((source_basename, src_file))

    for _source_basename, src_file in candidates:
        with open(src_file) as f:
            src_content = f.read()
        src_lines = src_content.split("\n")
        src_theorems = parse_theorems(src_lines)

        for sthm in src_theorems:
            if sthm.name == target_thm_name and sthm.has_proof:
                # Use the proof-extraction helper (handles inline proofs like
                # 'LEMMA Foo == x  BY DEF y' without re-declaring the theorem).
                proof_lines = get_theorem_proof_lines(src_lines, sthm)
                # Trim trailing empty lines and comment-only lines
                while proof_lines and (not proof_lines[-1].strip() or proof_lines[-1].strip().startswith("(*")):
                    proof_lines.pop()
                found_proof = (src_file, proof_lines)
                result.source_file = os.path.relpath(src_file, SOURCE_ROOT)
                break

        if found_proof:
            break

    if not found_proof:
        result.proof_found = False
        result.error = f"Could not find original proof for {target_thm_name}"
        return result

    result.proof_found = True
    src_file, proof_lines = found_proof

    # Count proof lines
    result.proof_lines_count = count_proof_lines(proof_lines)

    # Port the proof
    ported_content = port_proof_to_benchmark(benchmark_path, proof_lines)
    result.proof_ported = True

    proof_text = "\n".join(proof_lines)

    # Write ported content to a temp file and run tlapm
    tmp_dir = tempfile.mkdtemp(prefix="tlaps_validate_")
    try:
        tmp_file = os.path.join(tmp_dir, basename)
        with open(tmp_file, "w") as f:
            f.write(ported_content)

        # Copy dependency files (non-benchmark .tla files in the same directory)
        bench_dir = os.path.dirname(benchmark_path)
        for dep_file in glob.glob(os.path.join(bench_dir, "*.tla")):
            dep_basename = os.path.basename(dep_file)
            if dep_basename != basename and "_" not in os.path.splitext(dep_basename)[0]:
                shutil.copy2(dep_file, os.path.join(tmp_dir, dep_basename))

        exit_code, output, elapsed = run_tlapm(tmp_file, tlapm_path, tlapm_lib, timeout)
        result.tlapm_exit_code = exit_code
        result.tlapm_output = output
        result.tlapm_time_secs = elapsed
        result.tlapm_passed = exit_code == 0

        # Only check if source proof uses PROOF OMITTED (placeholder, not a real proof)
        from cheating_detection import detect_proof_omitted

        result.cheating_issues = detect_proof_omitted(proof_text)
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)

    return result


def generate_report(results: list[ValidationResult], output_path: str):
    """Generate a markdown report of validation results."""
    total = len(results)
    passed = sum(1 for r in results if r.status == "PASS")
    failed = sum(1 for r in results if r.status == "FAIL")
    cheating = sum(1 for r in results if r.status == "OMITTED")
    errors = sum(1 for r in results if r.status == "ERROR")
    no_proof = sum(1 for r in results if r.status == "NO_PROOF")

    total_time = sum(r.tlapm_time_secs for r in results)

    lines = []
    lines.append("# TLAPS Benchmark Validation Report\n")
    lines.append(f"**Generated**: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
    lines.append("## Summary\n")
    lines.append("| Metric | Count |")
    lines.append("|--------|-------|")
    lines.append(f"| Total benchmarks | {total} |")
    lines.append(f"| ✅ Passed | {passed} |")
    lines.append(f"| ❌ Failed | {failed} |")
    lines.append(f"| ⏭️ Placeholder (PROOF OMITTED) | {cheating} |")
    lines.append(f"| 🔍 No proof found | {no_proof} |")
    lines.append(f"| 💥 Error | {errors} |")
    lines.append(f"| ⏱️ Total verification time | {total_time:.1f}s |")
    total_proof_lines = sum(r.proof_lines_count for r in results)
    lines.append(f"| 📝 Total baseline proof lines | {total_proof_lines} |")
    lines.append("")

    # Group by module
    modules = {}
    for r in results:
        modules.setdefault(r.module, []).append(r)

    lines.append("## Results by Module\n")

    for module in sorted(modules.keys()):
        mod_results = modules[module]
        mod_pass = sum(1 for r in mod_results if r.status == "PASS")
        mod_total = len(mod_results)
        lines.append(f"### {module} ({mod_pass}/{mod_total} passed)\n")
        lines.append("| Theorem | Source | Status | Proof Lines | Time | Notes |")
        lines.append("|---------|--------|--------|-------------|------|-------|")

        for r in sorted(mod_results, key=lambda x: x.theorem_name):
            status_icon = {
                "PASS": "✅",
                "FAIL": "❌",
                "OMITTED": "⏭️",
                "ERROR": "💥",
                "NO_PROOF": "🔍",
            }.get(r.status, "❓")

            notes = ""
            if r.cheating_issues:
                notes = "; ".join(f"{c.kind}: {c.description}" for c in r.cheating_issues)
            elif r.error:
                notes = r.error
            elif r.status == "FAIL":
                # Extract failure summary from tlapm output
                fail_match = re.search(r"(\d+)/(\d+) obligation", r.tlapm_output)
                if fail_match:
                    notes = f"{fail_match.group(1)}/{fail_match.group(2)} obligations failed"
                elif "TIMEOUT" in r.tlapm_output:
                    notes = "Timeout"

            time_str = f"{r.tlapm_time_secs:.1f}s" if r.tlapm_time_secs > 0 else "-"
            source = r.source_file if r.source_file else "-"

            lines.append(
                f"| `{r.theorem_name}` | `{source}` | {status_icon} {r.status} | {r.proof_lines_count} | {time_str} | {notes} |"
            )

        lines.append("")

    # Placeholder details section
    placeholder_results = [r for r in results if r.cheating_issues]
    if placeholder_results:
        lines.append("## Placeholder Proofs (PROOF OMITTED in source)\n")
        lines.append(f"{len(placeholder_results)} benchmarks have source proofs that use PROOF OMITTED.\n")

    # Failed details section
    failed_results = [r for r in results if r.status == "FAIL"]
    if failed_results:
        lines.append("## Failed Verification Details\n")
        for r in failed_results:
            lines.append(f"### `{r.benchmark_file}`\n")
            # Show relevant tlapm output (last few error lines)
            error_lines = [ln for ln in r.tlapm_output.split("\n") if "ERROR" in ln or "obligation" in ln]
            if error_lines:
                lines.append("```")
                for el in error_lines[-5:]:
                    lines.append(el)
                lines.append("```")
            lines.append("")

    report = "\n".join(lines)
    with open(output_path, "w") as f:
        f.write(report)

    return report


def main():
    parser = argparse.ArgumentParser(description="Validate TLAPS benchmarks")
    parser.add_argument("--tlapm", default=None, help="Path to tlapm binary")
    parser.add_argument("--tlapm-lib", default=None, help="Path to tlapm lib directory")
    parser.add_argument("--timeout", type=int, default=120, help="Timeout per benchmark (seconds)")
    parser.add_argument("--jobs", type=int, default=4, help="Parallel jobs")
    parser.add_argument("--output", default="benchmark_report.md", help="Output report path")
    parser.add_argument("--filter", default=None, help="Only run benchmarks matching this pattern")
    parser.add_argument("--rerun-timeout", type=int, default=300, help="Timeout for rerun of failed benchmarks")
    parser.add_argument("--rerun-tlapm", default=None, help="Path to alternative tlapm for rerun (e.g. tlapm 1.6)")
    parser.add_argument("--rerun-tlapm-lib", default=None, help="Path to alternative tlapm lib for rerun")
    parser.add_argument("--rerun", action="store_true", help="Rerun failed benchmarks (optionally with --rerun-tlapm)")
    args = parser.parse_args()

    # Find tlapm
    tlapm_path = args.tlapm
    if not tlapm_path:
        # Try common locations
        candidates = [
            "/opt/tlapm/bin/tlapm",
            os.path.expanduser("~/.tlapm/bin/tlapm"),
            "/tmp/tlapm/bin/tlapm",
            shutil.which("tlapm"),
        ]
        for candidate in candidates:
            if candidate and os.path.isfile(candidate):
                tlapm_path = candidate
                break
    if not tlapm_path or not os.path.isfile(tlapm_path):
        print("ERROR: tlapm not found. Use --tlapm to specify path.")
        sys.exit(1)

    tlapm_lib = args.tlapm_lib or _derive_tlapm_lib(tlapm_path)
    if not tlapm_lib or not os.path.isdir(tlapm_lib):
        print(f"ERROR: tlapm lib not found near {tlapm_path}. Use --tlapm-lib to specify.")
        sys.exit(1)

    print(f"Using tlapm: {tlapm_path}")
    print(f"Using lib: {tlapm_lib}")

    # Build source file index: list of (module_name, filepath)
    source_files = []  # list of (mod_name, filepath)
    for mod_dir in find_source_dirs():
        module_path = os.path.join(SOURCE_ROOT, mod_dir)
        for f in find_tla_files(module_path):
            with open(f) as fh:
                content = fh.read()
            mod_name = parse_module_name(content)
            if mod_name:
                source_files.append((mod_name, f))

    # Find all benchmark files (exclude dependency copies that don't have '_' in name)
    benchmark_files = sorted(glob.glob(os.path.join(BENCHMARK_DIR, "**", "*.tla"), recursive=True))
    # Benchmark files have format SourceFile_TheoremName.tla (contain underscore)
    # Dependency copies are plain module names like Consensus.tla, VoteProof.tla
    benchmark_files = [f for f in benchmark_files if "_" in os.path.splitext(os.path.basename(f))[0]]
    if args.filter:
        benchmark_files = [f for f in benchmark_files if args.filter in f]

    print(f"Found {len(benchmark_files)} benchmark files to validate")

    # Prepare work items
    work_items = [(bf, source_files, tlapm_path, tlapm_lib, args.timeout) for bf in benchmark_files]

    # Run validation
    results = []
    start_time = time.time()
    counts = {"PASS": 0, "FAIL": 0, "OMITTED": 0, "ERROR": 0, "NO_PROOF": 0}

    def on_result(r, idx, total):
        counts[r.status] = counts.get(r.status, 0) + 1
        status_icon = {"PASS": "✅", "FAIL": "❌", "OMITTED": "⏭️", "ERROR": "💥", "NO_PROOF": "🔍"}.get(r.status, "❓")
        summary = f"[✅{counts['PASS']} ❌{counts['FAIL']} ⏭️{counts['OMITTED']} 💥{counts['ERROR']}]"
        print(f"  [{idx}/{total}] {status_icon} {r.benchmark_file} ({r.tlapm_time_secs:.1f}s)  {summary}", flush=True)

    if args.jobs == 1:
        for i, item in enumerate(work_items):
            r = validate_single_benchmark(item)
            results.append(r)
            on_result(r, i + 1, len(work_items))
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(validate_single_benchmark, item): item for item in work_items}
            for done_count, future in enumerate(as_completed(futures), start=1):
                r = future.result()
                results.append(r)
                on_result(r, done_count, len(work_items))

    total_time = time.time() - start_time

    # Parallel rerun of FAIL cases (optionally with different tlapm version)
    failed_results = [r for r in results if r.status == "FAIL"]
    rerun_tlapm = args.rerun_tlapm or tlapm_path
    rerun_tlapm_lib = args.rerun_tlapm_lib
    if not rerun_tlapm_lib and args.rerun_tlapm:
        rerun_tlapm_lib = _derive_tlapm_lib(rerun_tlapm)
    if not rerun_tlapm_lib:
        rerun_tlapm_lib = tlapm_lib

    if failed_results and args.rerun:
        using_alt = rerun_tlapm != tlapm_path
        label = f"rerun with {rerun_tlapm}" if using_alt else "rerun"
        print(f"\n{'=' * 60}")
        print(f"Parallel {label} of {len(failed_results)} failed benchmarks (timeout={args.rerun_timeout}s)")
        print(f"{'=' * 60}", flush=True)

        rerun_items = []
        for r in failed_results:
            bench_path = os.path.join(PROJECT_ROOT, r.benchmark_file)
            rerun_items.append((bench_path, source_files, rerun_tlapm, rerun_tlapm_lib, args.rerun_timeout))

        rerun_fixed = 0
        rerun_results = []
        if args.jobs == 1:
            for i, item in enumerate(rerun_items):
                r2 = validate_single_benchmark(item)
                rerun_results.append((failed_results[i], r2))
        else:
            with ProcessPoolExecutor(max_workers=args.jobs) as executor:
                futures = {executor.submit(validate_single_benchmark, item): i for i, item in enumerate(rerun_items)}
                for future in as_completed(futures):
                    i = futures[future]
                    r2 = future.result()
                    rerun_results.append((failed_results[i], r2))

        # Sort by original order and print
        rerun_results.sort(key=lambda x: x[1].tlapm_time_secs)
        for idx, (r_orig, r2) in enumerate(rerun_results):
            now_icon = {"PASS": "✅", "FAIL": "❌", "OMITTED": "⏭️", "ERROR": "💥"}.get(r2.status, "❓")
            print(
                f"  [{idx + 1}/{len(rerun_results)}] ❌→{now_icon} {r2.benchmark_file} ({r2.tlapm_time_secs:.1f}s)",
                flush=True,
            )
            if r2.status != r_orig.status:
                results[results.index(r_orig)] = r2
                if r2.status == "PASS":
                    rerun_fixed += 1

        print(f"  Rerun fixed {rerun_fixed}/{len(failed_results)} failures")
        total_time = time.time() - start_time

    # Sort results by module and name for report
    results.sort(key=lambda r: (r.module, r.theorem_name))

    # Generate report
    report_path = os.path.join(PROJECT_ROOT, args.output)
    generate_report(results, report_path)

    print(f"\n{'=' * 60}")
    print(f"Validation complete in {total_time:.1f}s")
    print(f"Report written to: {report_path}")

    # Print summary
    passed = sum(1 for r in results if r.status == "PASS")
    failed = sum(1 for r in results if r.status == "FAIL")
    cheating = sum(1 for r in results if r.status == "OMITTED")
    errors = sum(1 for r in results if r.status == "ERROR")
    print(f"\n✅ Passed: {passed}  ❌ Failed: {failed}  ⏭️ Placeholder: {cheating}  💥 Error: {errors}")


if __name__ == "__main__":
    main()
