#!/usr/bin/env python3
"""SANY input gate / audit for generated benchmark task files.

Every task file handed to an agent must parse under standalone tla2sany — the
canonical TLA+ parser, which is stricter than tlapm's own (e.g. it rejects an
operator parameter that shadows a state VARIABLE, which the model-split EXTENDS
layout turns into a cross-module multiply-definition). This module is the single
SANY-validity check used two ways:

  * post-generation gate — the proof-completion/proof-from-scratch generators call ``gate()`` on their output;
  * standalone audit     — ``python3 src/dataset/sany_audit.py benchmark``.

Policy: a SANY-failing task is FLAGGED (written to a manifest + the audit log),
never silently dropped — a human reviews it.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed

from tlacore.sany.dump import SanyError, dump_normalized

# Mirror Mode.is_benchmark_file (src/evaluator/modes/base.py): a task file has
# an underscore in its module name AND states a top-level proof goal; a shared
# model / dependency layer does not. Kept deliberately in sync with that rule.
_TOP_LEVEL_GOAL = re.compile(r"^[ \t]*(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", re.MULTILINE)


def is_task_file(path: str) -> bool:
    name = os.path.splitext(os.path.basename(path))[0]
    if "_" not in name:
        return False
    try:
        with open(path, encoding="utf-8", errors="ignore") as f:
            return _TOP_LEVEL_GOAL.search(f.read()) is not None
    except OSError:
        return False


def validate_task(path: str, dep_dir: str | None = None, timeout: int = 120) -> tuple[bool, str]:
    """Return ``(ok, error)``. ``ok`` is True iff standalone SANY parses the task
    with its sibling dependency modules supplied (so a parse error inside a
    dependency surfaces too)."""
    dep_dir = dep_dir or os.path.dirname(path)
    try:
        dump_normalized(path, dep_dir=dep_dir, timeout=timeout)
        return True, ""
    except SanyError as e:
        return False, str(e).replace("\n", " ")
    except Exception as e:  # subprocess timeout / OSError
        return False, f"{type(e).__name__}: {e}"


def audit_dir(directory: str, *, timeout: int = 120, jobs: int = 16) -> tuple[int, list[tuple[str, str]]]:
    """SANY-validate every task file under ``directory`` in parallel.

    Returns ``(total_tasks, failures)`` where ``failures`` is a sorted list of
    ``(path, error)``."""
    tasks = [p for p in _walk_tla(directory) if is_task_file(p)]
    failures: list[tuple[str, str]] = []
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(validate_task, p, None, timeout): p for p in tasks}
        for fut in as_completed(futs):
            ok, err = fut.result()
            if not ok:
                failures.append((futs[fut], err))
    return len(tasks), sorted(failures)


def _walk_tla(directory: str):
    for root, dirs, files in os.walk(directory):
        # Prune hidden dirs (.tlacache, .git, ...) in place — they hold build
        # artifacts / stale .tla copies, not benchmark tasks. This matches
        # glob('**')'s default of not descending into dotdirs, so the gate sees
        # exactly the runner's task set.
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        for f in files:
            if f.endswith(".tla"):
                yield os.path.join(root, f)


def gate(directory, *, manifest_path=None, audit_writer=None, label="sany-gate") -> list[tuple[str, str]]:
    """Post-generation gate: SANY-validate ``directory``, write a manifest of
    failures, optionally append them to an open audit-log writer, print a
    one-line summary. FLAGS, does not drop. Returns the failures list."""
    total, failures = audit_dir(directory)
    manifest_path = manifest_path or os.path.join(directory, "sany_flagged.json")
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "total_tasks": total,
                "flagged": len(failures),
                "failures": [{"file": os.path.relpath(p, directory), "error": e[:400]} for p, e in failures],
            },
            f,
            indent=2,
        )
    if failures:
        print(f"⚠️  [{label}] {len(failures)}/{total} task(s) FAILED standalone SANY — flagged in {manifest_path}")
        for p, e in failures:
            line = f"[{label}] SANY-FAIL {os.path.relpath(p, directory)}: {e[:200]}"
            print("   " + line)
            if audit_writer:
                audit_writer.write(line + "\n")
    else:
        print(f"✓ [{label}] all {total} task(s) pass standalone SANY")
    return failures


def main():
    ap = argparse.ArgumentParser(description="SANY-validate benchmark task files (flag, do not drop).")
    ap.add_argument("directory", nargs="?", default="benchmark", help="Benchmark dir to audit (default: benchmark)")
    ap.add_argument("--manifest", default=None, help="Manifest output path (default: <dir>/sany_flagged.json)")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--jobs", type=int, default=16)
    args = ap.parse_args()
    failures = gate(args.directory, manifest_path=args.manifest)
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
