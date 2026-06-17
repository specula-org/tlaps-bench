"""Detect modification of a GIVEN dependency module.

The prompt forbids editing the provided dependency files. We compare each given
dependency present in the solution dir against its canonical copy in the
benchmark directory; any byte difference is a violation. (Agent-created modules
are a separate concern — see ``smuggled_module``.)
"""

from __future__ import annotations

import os

from ..context import CheckContext
from ..issue import Issue, Severity

name = "DEPENDENCY_MODIFIED"


def check(ctx: CheckContext) -> list[Issue]:
    # The canonical dependency contents live in the benchmark dir, recorded on
    # the context. Given module names come from provenance.
    bdir = ctx.benchmark_dir
    if not bdir or not os.path.isdir(bdir):
        return []
    issues: list[Issue] = []
    for mod in ctx.provenance.given:
        sol_f = os.path.join(ctx.solution_dir, f"{mod}.tla")
        can_f = os.path.join(bdir, f"{mod}.tla")
        if not (os.path.exists(sol_f) and os.path.exists(can_f)):
            continue
        try:
            with open(sol_f, encoding="utf-8", errors="ignore") as _sf:
                a = _sf.read()
            with open(can_f, encoding="utf-8", errors="ignore") as _cf:
                b = _cf.read()
        except OSError:
            continue
        if a != b:
            issues.append(
                Issue(
                    vector=name,
                    severity=Severity.CHEATING,
                    message=f"Given dependency '{mod}.tla' was modified — not allowed.",
                    location=f"{mod}.tla",
                )
            )
    return issues
