"""Detect the agent weakening/altering the target theorem's statement.

The agent may add helper lemmas, but must not change what the target theorem
*claims*. We compare, by normalized statement text, the theorems present in the
baseline (which is just the model + the target) against the solution. If a
baseline theorem's statement no longer appears verbatim in the solution, the
statement was modified.

Line numbers shift when the agent inserts helpers, so we compare statement TEXT
(whitespace-normalized), sliced from each file by SANY's ``statement_loc`` — not
positions.
"""

from __future__ import annotations

import os
import re

from tlacore.source import slice_loc

from ..context import CheckContext
from ..issue import Issue, Severity

name = "STATEMENT_MODIFIED"

_WS = re.compile(r"\s+")


def _norm(text: str) -> str:
    return _WS.sub(" ", text).strip()


def _statement_texts(module, source: str) -> dict[str, str]:
    """Map theorem display-name -> normalized statement text."""
    out = {}
    for t in module.theorems:
        if t.statement_loc:
            out[t.display_name] = _norm(slice_loc(source, t.statement_loc))
    return out


def check(ctx: CheckContext) -> list[Issue]:
    if ctx.baseline is None:
        return []
    # Read the actual files from the solution dir; module.source_file may point
    # at a now-deleted temp dir (we parse normalized copies there).
    base_src = _read(os.path.join(ctx.solution_dir, "benchmark.tla"))
    sol_src = _read(os.path.join(ctx.solution_dir, ctx.target_name + ".tla")) or _read(
        os.path.join(ctx.solution_dir, "solution.tla")
    )
    if not base_src or not sol_src:
        return []

    base_stmts = set(_statement_texts(ctx.baseline, base_src).values())
    sol_stmts = set(_statement_texts(ctx.solution, sol_src).values())

    issues: list[Issue] = []
    for stmt in base_stmts:
        if stmt and stmt not in sol_stmts:
            issues.append(
                Issue(
                    vector=name,
                    severity=Severity.CHEATING,
                    message=(
                        "A baseline theorem statement no longer appears verbatim "
                        "in the solution — target may have been weakened/altered."
                    ),
                    location=ctx.solution.filename,
                    evidence=stmt[:120],
                )
            )
    return issues


def _read(path):
    if not path or not os.path.exists(path):
        return None
    try:
        return open(path, encoding="utf-8", errors="ignore").read()
    except OSError:
        return None
