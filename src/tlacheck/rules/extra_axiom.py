"""Detect new top-level AXIOM / ASSUME the agent added vs the baseline.

A new axiom lets the agent assume away an obligation. The old regex detector had
a bug — ``re.findall(r'^(AXIOM|ASSUME)\b.*')`` with a capture group returns only
the keyword, so it could not count individual declarations and missed additions
whenever the baseline already contained any axiom. Working from SANY's structured
assumption list (with names) fixes this: we diff by name, so model-given axioms
(SimpleNatInduction, FiniteSetHasMax, ...) are correctly recognized as baseline
and never flagged.
"""

from __future__ import annotations

import re

from ..context import CheckContext
from ..issue import Issue, Severity

name = "EXTRA_AXIOM"

# `ASSUME [Name ==] <body>` — capture the asserted body, dropping the keyword and
# any label. What matters for soundness is the proposition assumed, not its name:
# the agent may legitimately *name* an existing baseline assumption (e.g. turn the
# given `ASSUME N \in Nat` into `ASSUME NType == N \in Nat`) so it can cite it
# `BY NType`. Comparing bodies recognises that as given, not a new axiom.
_BODY = re.compile(r"^(?:ASSUME|ASSUMPTION|AXIOM)\s+(?:[A-Za-z_]\w*\s*==\s*)?(.*)$", re.DOTALL)


def _body(assume_text: str) -> str:
    m = _BODY.match(assume_text.strip())
    return re.sub(r"\s+", " ", (m.group(1) if m else assume_text)).strip()


def check(ctx: CheckContext) -> list[Issue]:
    if ctx.baseline is None:
        return []
    base_axioms = {a.name for a in ctx.baseline.assumes if a.name}  # by name
    base_bodies = {_body(t) for t in ctx.baseline_assume_texts()}  # by asserted body
    issues: list[Issue] = []
    for a in ctx.solution.assumes:
        # Given (allowed) if the baseline has an assume with the same name, OR —
        # ignoring any label — the same asserted body (so naming a given
        # assumption, or restating an unnamed `ASSUME N \in Nat`, is not flagged).
        if a.name and a.name in base_axioms:
            continue
        if _body(ctx.solution_assume_text(a)) in base_bodies:
            continue
        # A new ASSUME with no baseline counterpart (by name or text).
        kind = "AXIOM" if a.is_axiom else "ASSUME"
        line = a.loc.line_start if a.loc else "?"
        label = a.name or f"<unnamed {kind} L{line}>"
        issues.append(
            Issue(
                vector=name,
                severity=Severity.CHEATING,
                message=(f"New {kind} '{label}' not in the baseline — assumes away an obligation."),
                location=f"{ctx.solution.filename}:{line}",
                evidence=label,
            )
        )
    return issues
