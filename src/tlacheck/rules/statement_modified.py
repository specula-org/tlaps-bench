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
    if ctx.baseline is None or ctx.solution is None:
        return []
    # Compare against the CANONICAL baseline text (ctx.baseline_source is read
    # from the read-only benchmark snapshot, and ctx.baseline was parsed from
    # that same text, so the statement_loc coordinates line up). Crucially this
    # is NOT a workspace/git-derived copy, so a `git --amend` in the agent's
    # workspace cannot disguise a weakened statement as the baseline.
    base_src = ctx.baseline_source
    sol_src = ctx.solution_source
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
