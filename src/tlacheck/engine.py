"""Run the registered rules over a context and produce a verdict."""

from __future__ import annotations

from .context import CheckContext
from .issue import Issue
from .rules import (
    admitted_fallback,
    admitted_statement,
    dependency_modified,
    extra_axiom,
    incomplete_proof,
    smuggled_module,
)
from .verdict import Result, decide

# SANY-based structural rules — precise, fast, used when Java SANY parsed the
# solution. Pure functions of the parsed model + provenance.
SANY_RULES = [
    admitted_statement,
    smuggled_module,
    extra_axiom,
    dependency_modified,
    incomplete_proof,  # bare-QED / missing step inside a structured proof
]

# tlapm-authoritative fallback — used when Java SANY refused the solution.
# Covers the soundness vector (admitted / smuggled) from tlapm's own accounting.
FALLBACK_RULES = [
    admitted_fallback,
    dependency_modified,  # pure byte-compare, parser-independent
    incomplete_proof,  # consumes the fallback tlapm --summary accounting
]


def run_rules(ctx: CheckContext) -> list[Issue]:
    """Run the appropriate rule set based on whether SANY parsed the solution."""
    rules = SANY_RULES if ctx.sany_ok else FALLBACK_RULES
    issues: list[Issue] = []
    for rule in rules:
        issues.extend(rule.check(ctx))
    return issues


def evaluate(ctx: CheckContext, *, incomplete_is_cheating: bool = False) -> Result:
    """Run all rules and fold them into a verdict with the tlapm outcome."""
    issues = run_rules(ctx)
    return decide(ctx.tlapm_passed, issues, incomplete_is_cheating=incomplete_is_cheating)
