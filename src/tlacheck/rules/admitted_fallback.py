"""tlapm-authoritative fallback for the soundness vector (SANY-unparseable cases).

When Java SANY refuses the solution (it is stricter than tlapm — e.g. rejects
bound-variable shadowing tlapm accepts), the static SANY rules cannot run. tlapm
itself parsed the solution (it had to, to verify it), so we fall back to its
``--summary`` accounting: every admitted statement (bare theorem / PROOF OMITTED
/ bare QED) shows up as an "incomplete proof of theorem at line N".

Given (allowed) admitted lemmas — the L1 preamble's preceding OMITTED lemmas —
are subtracted by line: the agent only fills the target's proof and leaves the
preamble intact, so a given lemma keeps its line; a line-set diff against the
baseline summary isolates what the agent introduced.

Agent-created modules are summarized too; any incomplete proof there is a
smuggled axiom (same as the SANY-side smuggled_module rule).

This rule only contributes when ``ctx.sany_ok`` is False — otherwise the precise
SANY rules already cover (and exceed) it.
"""

from __future__ import annotations

from ..context import CheckContext
from ..issue import Issue, Severity

name = "ADMITTED_FALLBACK"


def check(ctx: CheckContext) -> list[Issue]:
    if ctx.sany_ok:
        return []
    issues: list[Issue] = []

    sol = ctx.summaries.get("")
    base = ctx.summaries.get("__baseline__")
    if sol is not None:
        given_lines = base.incomplete_lines() if base is not None else set()
        for ip in sol.incomplete:
            if ip.theorem_line in given_lines:
                continue  # given (baseline) admitted lemma — allowed
            issues.append(
                Issue(
                    vector=name,
                    severity=Severity.CHEATING,
                    message=(
                        f"[tlapm-fallback] Theorem at line {ip.theorem_line} is "
                        f"admitted (no real proof / bare QED) — not present in the "
                        f"baseline; admitted as an axiom."
                    ),
                    location=f"{ctx.target_name}:{ip.theorem_line}",
                )
            )

    # Agent-created modules: any admitted theorem is a smuggled axiom.
    for mod, summ in ctx.summaries.items():
        if mod in ("", "__baseline__") or summ is None:
            continue
        for ip in summ.incomplete:
            issues.append(
                Issue(
                    vector="SMUGGLED_MODULE",
                    severity=Severity.CHEATING,
                    message=(
                        f"[tlapm-fallback] Agent-created module '{mod}' has an "
                        f"admitted theorem at line {ip.theorem_line} — smuggled axiom."
                    ),
                    location=f"{mod}.tla:{ip.theorem_line}",
                )
            )
    return issues
