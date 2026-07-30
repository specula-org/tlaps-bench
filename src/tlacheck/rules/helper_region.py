"""Validate module-level declarations inside marked editable regions."""

from __future__ import annotations

from common.task_contract import (
    BEGIN_AGENT_HELPERS,
    END_AGENT_HELPERS,
    EditableRegionError,
    has_marker_line,
    parse_editable_regions,
    parse_proof_region,
)

from ..context import CheckContext
from ..issue import Issue, Severity

name = "HELPER_REGION_VIOLATION"


def _inside(loc, bounds: tuple[int, int]) -> bool:
    return loc is not None and bounds[0] <= loc.line_start <= bounds[1]


def _contained(loc, bounds: tuple[int, int]) -> bool:
    return _inside(loc, bounds) and loc.line_end <= bounds[1]


def _issue(
    message: str,
    line: int | None = None,
    evidence: str | None = None,
    *,
    region: str = "helper",
) -> Issue:
    return Issue(
        vector=name,
        severity=Severity.CHEATING,
        message=message,
        location=f"{region} region:{line}" if line else f"{region} region",
        evidence=evidence,
    )


def check(ctx: CheckContext) -> list[Issue]:
    """Allow safe helpers and keep module-level declarations out of proofs."""

    if not ctx.solution or not ctx.baseline_source:
        return []
    try:
        if has_marker_line(ctx.baseline_source, (BEGIN_AGENT_HELPERS, END_AGENT_HELPERS)):
            parse_editable_regions(ctx.baseline_source)
            submitted_regions = parse_editable_regions(ctx.solution_source)
            helper_bounds = submitted_regions.helper_line_bounds
        else:
            parse_proof_region(ctx.baseline_source)
            submitted_regions = parse_proof_region(ctx.solution_source)
            helper_bounds = None
    except EditableRegionError:
        return []  # The fixed-region integrity check owns malformed markers.

    proof_bounds = submitted_regions.proof_line_bounds

    issues: list[Issue] = []
    forbidden = (
        ("CONSTANT", ctx.solution.constants),
        ("VARIABLE", ctx.solution.variables),
        ("ASSUME/AXIOM", ctx.solution.assumes),
        ("INSTANCE", ctx.solution.instances),
    )
    if helper_bounds is not None:
        for kind, declarations in forbidden:
            for declaration in declarations:
                if _inside(declaration.loc, helper_bounds):
                    label = getattr(declaration, "name", None) or kind
                    issues.append(
                        _issue(
                            f"{kind} declarations are not allowed in the helper region",
                            declaration.loc.line_start,
                            str(label),
                        )
                    )

        for theorem in ctx.solution.theorems:
            if not _inside(theorem.loc, helper_bounds):
                continue
            if theorem.name is None:
                issues.append(
                    _issue(
                        "helper THEOREM/LEMMA declarations must be named",
                        theorem.loc.line_start,
                        theorem.display_name,
                    )
                )
            if theorem.is_admitted:
                issues.append(
                    _issue(
                        "helper THEOREM/LEMMA declarations must include a complete proof",
                        theorem.loc.line_start,
                        theorem.display_name,
                    )
                )

        allowed = (
            ("operator", ctx.solution.operators),
            ("THEOREM/LEMMA", ctx.solution.theorems),
            ("module directive", ctx.solution.directives),
        )
        for kind, declarations in allowed:
            for declaration in declarations:
                if _inside(declaration.loc, helper_bounds) and not _contained(declaration.loc, helper_bounds):
                    issues.append(
                        _issue(
                            f"{kind} declarations must be contained in the helper region",
                            declaration.loc.line_start,
                        )
                    )

    declarations = forbidden + (
        ("operator", ctx.solution.operators),
        ("THEOREM/LEMMA", ctx.solution.theorems),
        ("nested module", ctx.solution.inner_modules),
        ("module directive", ctx.solution.directives),
        ("unclassified top-level", ctx.solution.other_top_levels),
    )
    for kind, items in declarations:
        for declaration in items:
            if _inside(declaration.loc, proof_bounds):
                label = getattr(declaration, "name", None) or kind
                issues.append(
                    _issue(
                        f"module-level {kind} declarations are not allowed in the proof region",
                        declaration.loc.line_start,
                        str(label),
                        region="proof",
                    )
                )

    if helper_bounds is not None:
        for inner in ctx.solution.inner_modules:
            if _inside(inner.loc, helper_bounds):
                issues.append(
                    _issue(
                        "nested modules are not allowed in the helper region",
                        inner.loc.line_start,
                        inner.name,
                    )
                )

        for directive in ctx.solution.directives:
            if _inside(directive.loc, helper_bounds) and not directive.definitions_only:
                issues.append(
                    _issue(
                        f"module-level {directive.kind} directives in the helper region must use DEF",
                        directive.loc.line_start,
                    )
                )

        for node in ctx.solution.other_top_levels:
            if _inside(node.loc, helper_bounds):
                issues.append(
                    _issue(
                        "unclassified top-level declarations are not allowed in the helper region",
                        node.loc.line_start,
                        node.kind,
                    )
                )

    return issues
