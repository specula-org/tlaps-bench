"""Detect unjustified steps (e.g. bare QED) inside a structured proof.

The SANY top-level proof-node check (admitted_statement) sees a theorem that
HAS a proof but cannot see a bare QED buried inside that proof. tlapm's
``--summary`` does: it reports each theorem with missing proof steps. This rule
consumes that accounting (``ctx.summary``).

Severity is INCOMPLETE, not CHEATING: a bare QED on a trivial closing step (cf.
the borderline IsBijectionTransitive) is an incomplete proof, not necessarily a
deliberate cheat. Policy can elevate it via ``incomplete_is_cheating``.

To avoid double-counting, theorems already flagged as fully admitted (bare /
OMITTED) by ``admitted_statement`` are skipped here — those are CHEATING, and
this rule only adds the "has a real proof but with a hole" case.
"""

from __future__ import annotations

from ..context import CheckContext
from ..issue import Issue, Severity

name = "INCOMPLETE_PROOF"


def check(ctx: CheckContext) -> list[Issue]:
    if ctx.summary is None:
        return []  # requires a tlapm --summary run; opt-in

    # Lines of theorems that are fully admitted (no proof / OMITTED) — covered
    # by admitted_statement as CHEATING; don't also report them as INCOMPLETE.
    # ctx.solution is None on the tlapm fallback path (SANY couldn't parse); the
    # admitted theorems are then surfaced by admitted_fallback instead.
    admitted_lines = (
        {t.loc.line_start for t in ctx.solution.theorems if t.is_admitted and t.loc}
        if ctx.solution is not None
        else set()
    )
    issues: list[Issue] = []
    sol_name = ctx.solution.filename if ctx.solution is not None else ctx.target_name
    for ip in ctx.summary.incomplete:
        if ip.theorem_line in admitted_lines:
            continue
        locs = ", ".join(str(x) for x in ip.missing_lines) or "?"
        issues.append(
            Issue(
                vector=name,
                severity=Severity.INCOMPLETE,
                message=(
                    f"Theorem at line {ip.theorem_line} has {ip.missing_count} "
                    f"unjustified step(s) (bare QED / missing proof) at line(s) {locs}."
                ),
                location=f"{sol_name}:{ip.theorem_line}",
            )
        )
    return issues
