"""Command-line entry point for the cheat auditor.

Audit one submission (or a tree of them) for cheating, on the SANY semantic
model. Fast path uses only the static structural rules (no tlapm). Pass
``--summary`` to additionally run ``tlapm --summary`` for bare-QED / incomplete
detection.

Usage:
    python -m tlacheck.cli <solution_dir> --target NAME --benchmark-dir DIR
    python -m tlacheck.cli --scan results/level2 --benchmark-root benchmark

Exit code: 0 = clean (PASS/no cheating), 2 = cheating found, 3 = error.
"""

from __future__ import annotations

import argparse
import glob
import os
import sys

from .context import build_context
from .engine import run_rules
from .issue import Severity


def audit_one(solution_dir: str, target: str, benchmark_dir: str | None, with_summary: bool = False) -> list:
    # incomplete_proof is wired into the engine rule sets; it only fires when a
    # tlapm --summary is available, so request one when --summary was passed.
    ctx = build_context(solution_dir, target, benchmark_dir=benchmark_dir, compute_summary=with_summary)
    return run_rules(ctx)


def _infer(bdir: str, benchmark_root: str | None):
    """From a result benchmark dir, infer (target, benchmark_dir)."""
    name = os.path.basename(bdir.rstrip("/"))
    group = os.path.basename(os.path.dirname(bdir.rstrip("/")))
    # find the enclosing level (level1/level2) in the path
    parts = bdir.split(os.sep)
    level = next((p for p in parts if p in ("level1", "level2")), None)
    bench_dir = None
    if benchmark_root and level:
        bench_dir = os.path.join(benchmark_root, level, group)
    return name, bench_dir


def main(argv=None):
    ap = argparse.ArgumentParser(description="TLA+ proof cheat auditor (SANY-based)")
    ap.add_argument("solution_dir", nargs="?", help="a single benchmark result dir")
    ap.add_argument("--target", help="benchmark module name (else inferred)")
    ap.add_argument("--benchmark-dir", help="canonical benchmark/<level>/<module>/ dir")
    ap.add_argument("--scan", help="recursively audit all benchmark dirs under this path")
    ap.add_argument(
        "--benchmark-root", default="benchmark", help="root of canonical benchmarks (for --scan provenance)"
    )
    ap.add_argument("--summary", action="store_true", help="also run tlapm --summary for incomplete-proof detection")
    args = ap.parse_args(argv)

    targets = []
    if args.scan:
        for bdir in glob.glob(os.path.join(args.scan, "*/2*/*/*")):
            if os.path.isdir(bdir) and glob.glob(os.path.join(bdir, "*.tla")):
                name, bench = _infer(bdir, args.benchmark_root)
                targets.append((bdir, name, bench))
    elif args.solution_dir:
        name = args.target or _infer(args.solution_dir, args.benchmark_root)[0]
        bench = args.benchmark_dir or _infer(args.solution_dir, args.benchmark_root)[1]
        targets.append((args.solution_dir, name, bench))
    else:
        ap.error("provide a solution_dir or --scan")

    any_cheat = False
    n_clean = n_cheat = n_err = 0
    for sdir, name, bench in sorted(targets):
        try:
            issues = audit_one(sdir, name, bench, with_summary=args.summary)
        except Exception as e:
            n_err += 1
            print(f"  ERROR  {sdir}: {str(e)[:100]}")
            continue
        cheating = [i for i in issues if i.severity is Severity.CHEATING]
        if cheating:
            any_cheat = True
            n_cheat += 1
            print(f"  CHEATING  {sdir}")
            for i in issues:
                print(f"       {i}")
        else:
            n_clean += 1
            if not args.scan:
                print(f"  CLEAN  {sdir}")
    if args.scan:
        print(f"\n=== clean {n_clean} | cheating {n_cheat} | error {n_err} ===")
    return 2 if any_cheat else 0


if __name__ == "__main__":
    sys.exit(main())
