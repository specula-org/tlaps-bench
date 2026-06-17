"""Aggregate issues + tlapm result into a final verdict."""

from __future__ import annotations

import enum
from dataclasses import dataclass, field

from .issue import Issue, Severity


class Verdict(enum.Enum):
    PASS = "PASS"  # tlapm proved it AND no cheating
    FAIL = "FAIL"  # tlapm did not prove it
    CHEATING = "CHEATING"  # tlapm "passed" but a CHEATING issue was found
    INCOMPLETE = "INCOMPLETE"  # tlapm "passed" but proof has unjustified steps
    ERROR = "ERROR"  # could not run the check


@dataclass
class Result:
    verdict: Verdict
    issues: list[Issue] = field(default_factory=list)
    detail: str = ""

    @property
    def cheating_issues(self) -> list[Issue]:
        return [i for i in self.issues if i.severity is Severity.CHEATING]

    @property
    def incomplete_issues(self) -> list[Issue]:
        return [i for i in self.issues if i.severity is Severity.INCOMPLETE]


def decide(tlapm_passed: bool, issues: list[Issue], *, incomplete_is_cheating: bool = False) -> Result:
    """Combine the tlapm outcome with detected issues into a verdict.

    Cheating always wins (even if tlapm "passed" — that is precisely the danger).
    INCOMPLETE is reported separately unless policy elevates it to cheating.
    """
    cheating = [i for i in issues if i.severity is Severity.CHEATING]
    incomplete = [i for i in issues if i.severity is Severity.INCOMPLETE]

    if cheating:
        return Result(Verdict.CHEATING, issues, detail=f"{len(cheating)} cheating issue(s)")
    if incomplete and incomplete_is_cheating:
        return Result(Verdict.CHEATING, issues, detail="incomplete proof treated as cheating (policy)")
    if not tlapm_passed:
        return Result(Verdict.FAIL, issues, detail="tlapm did not prove the goal")
    if incomplete:
        return Result(Verdict.INCOMPLETE, issues, detail=f"{len(incomplete)} unjustified step(s)")
    return Result(Verdict.PASS, issues)
