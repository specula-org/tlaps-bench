#!/usr/bin/env python3
"""Triviality (degenerate-placeholder) gate / audit for benchmark task files.

A task is DEGENERATE when tlapm discharges it with the ``PROOF OBVIOUS``
placeholder untouched — the target goal lies within one backend call of the
auto-usable context (module AXIOMs plus the backends' built-in theories), so
the grader PASSes a no-op submission and the task measures nothing. The
2026-07 audit found 21 such tasks (SequencesTheorems_*, PaxosProof_OtherMessage,
TwoPhase_Mod2, *_SubSeqInRange), one of which turned a zero-token copilot
startup failure into a scored PASS.

This is the same tlapm invocation and completeness reading the grader uses
(``tlapm --strict`` + ``parse_strict_status``), so "the placeholder fails
here" is exactly "an unchanged file cannot PASS grading". Whether a goal is
one-call-reachable depends on the installed backends, so the gate must be
re-run after a tlapm upgrade. Used two ways, mirroring sany_audit:

  * post-generation gate — generators call ``gate(drop=True)`` on their output;
  * standalone audit     — ``python3 src/dataset/triviality_audit.py benchmark``.

Policy: unlike sany_audit, a degenerate task is not a bug to fix by hand — the
placeholder verifying IS "a no-op submission PASSes", so the task is worthless.
The generators call ``gate(drop=True)`` to DELETE flagged tasks, making
regeneration self-healing (the source theorem stays, but its degenerate task
never re-ships); the manifest + audit log record every drop, so it is never
silent. The standalone CLI defaults to audit-only (report + exit 1) so CI can
detect a regression; ``--drop`` removes them. A per-file timeout counts as
non-degenerate (the placeholder did not verify within budget; a lower bound), so
a genuine task is never dropped.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed

from common.check_proof import (
    find_community_lib,
    find_proof_obvious_line,
    find_tlapm,
    find_tlapm_lib,
    parse_strict_status,
    run_killgroup,
)


def is_placeholder_task(path: str) -> bool:
    """A file this gate applies to: it carries the ``PROOF OBVIOUS`` stub."""
    try:
        with open(path, encoding="utf-8", errors="ignore") as f:
            return find_proof_obvious_line(f.read().split("\n")) is not None
    except OSError:
        return False


def check_task(path: str, tlapm_path: str, tlapm_lib: str, timeout: int = 120) -> tuple[bool, str]:
    """Return ``(degenerate, detail)``. Degenerate iff the grader's own
    completeness reading accepts the file untouched."""
    tmp = tempfile.mkdtemp(prefix="triviality_gate_")
    try:
        base = os.path.basename(path)
        shutil.copy2(path, os.path.join(tmp, base))
        for dep in glob.glob(os.path.join(os.path.dirname(path), "*.tla")):
            if os.path.basename(dep) != base:
                shutil.copy2(dep, os.path.join(tmp, os.path.basename(dep)))
        cmd = [tlapm_path, "--strict", "-I", tlapm_lib]
        community_lib = find_community_lib(path)
        if community_lib:
            cmd += ["-I", community_lib]
        cmd.append(os.path.join(tmp, base))
        try:
            out, err, rc = run_killgroup(cmd, timeout, tmp)
        except subprocess.TimeoutExpired:
            return False, "timeout (placeholder did not verify within budget)"
        complete, _n_missing, _failed = parse_strict_status(rc, out + err)
        if complete:
            return True, "placeholder PROOF OBVIOUS verifies unchanged — no-op submission would PASS"
        return False, ""
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def audit_dir(directory: str, *, timeout: int = 120, jobs: int = 16) -> tuple[int, list[tuple[str, str]]]:
    """Check every placeholder task under ``directory`` in parallel.

    Returns ``(total_tasks, flagged)`` where ``flagged`` is a sorted list of
    ``(path, detail)`` for degenerate tasks."""
    tlapm_path = find_tlapm()
    if not tlapm_path:
        raise RuntimeError("tlapm not found — cannot run the triviality gate")
    tlapm_lib = find_tlapm_lib(tlapm_path)
    if not tlapm_lib:
        raise RuntimeError("tlapm lib not found — cannot run the triviality gate")
    tasks = [p for p in _walk_tla(directory) if is_placeholder_task(p)]
    flagged: list[tuple[str, str]] = []
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(check_task, p, tlapm_path, tlapm_lib, timeout): p for p in tasks}
        for fut in as_completed(futs):
            degenerate, detail = fut.result()
            if degenerate:
                flagged.append((futs[fut], detail))
    return len(tasks), sorted(flagged)


def _walk_tla(directory: str):
    for root, dirs, files in os.walk(directory):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        for f in files:
            if f.endswith(".tla"):
                yield os.path.join(root, f)


def gate(
    directory, *, manifest_path=None, audit_writer=None, label="triviality-gate", timeout=120, jobs=16, drop=False
):
    """Post-generation gate: find degenerate tasks under ``directory``, write a
    manifest, optionally append to an audit-log writer, print a one-line summary.
    Returns the flagged list.

    Unlike the SANY gate, a degenerate task is not a bug to fix by hand — the
    placeholder verifying IS "a no-op submission PASSes", so the task is worthless
    and must not ship. With ``drop=True`` (how the generators call it) the flagged
    files are DELETED, making regeneration self-healing: the source theorem stays,
    but its degenerate task never survives a fresh generation. ``drop=False`` (the
    standalone audit default) only reports, so CI can detect a regression. A
    timeout counts as non-degenerate, so a genuine task is never dropped.
    """
    total, flagged = audit_dir(directory, timeout=timeout, jobs=jobs)
    manifest_path = manifest_path or os.path.join(directory, "triviality_flagged.json")
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "total_tasks": total,
                "flagged": len(flagged),
                "dropped": drop,
                "failures": [{"file": os.path.relpath(p, directory), "error": e[:400]} for p, e in flagged],
            },
            f,
            indent=2,
        )
    if flagged:
        verb = "DROPPED" if drop else "DEGENERATE"
        action = "dropped" if drop else "flagged"
        print(
            f"⚠️  [{label}] {len(flagged)}/{total} task(s) DEGENERATE (pass unchanged) — {action} (manifest {manifest_path})"
        )
        for p, e in flagged:
            if drop:
                os.remove(p)
            line = f"[{label}] {verb} {os.path.relpath(p, directory)}: {e[:200]}"
            print("   " + line)
            if audit_writer:
                audit_writer.write(line + "\n")
    else:
        print(f"✓ [{label}] all {total} task(s) fail their placeholder (non-degenerate)")
    return flagged


def main():
    ap = argparse.ArgumentParser(description="Flag benchmark tasks whose PROOF OBVIOUS placeholder already verifies.")
    ap.add_argument("directory", nargs="?", default="benchmark", help="Benchmark dir to audit (default: benchmark)")
    ap.add_argument("--manifest", default=None, help="Manifest output path (default: <dir>/triviality_flagged.json)")
    ap.add_argument("--timeout", type=int, default=120, help="Per-file tlapm budget in seconds")
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--drop", action="store_true", help="Delete degenerate tasks (default: audit-only, exit 1 if any)")
    args = ap.parse_args()
    flagged = gate(args.directory, manifest_path=args.manifest, timeout=args.timeout, jobs=args.jobs, drop=args.drop)
    # Audit mode signals a regression (exit 1); drop mode resolved it (exit 0).
    sys.exit(1 if flagged and not args.drop else 0)


if __name__ == "__main__":
    main()
