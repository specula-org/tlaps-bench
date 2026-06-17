"""The unit of a cheat-detection finding."""

from __future__ import annotations

import enum
from dataclasses import dataclass


class Severity(enum.Enum):
    """How a finding affects the verdict.

    CHEATING   — deliberate soundness violation (admitted statement the proof
                 leans on, smuggled module, new axiom, weakened statement).
                 Makes the verdict CHEATING.
    INCOMPLETE — the proof has an unjustified step (e.g. a bare QED) but is not
                 a clear deliberate cheat. Policy choice whether to fail; by
                 default surfaced separately, not counted as CHEATING.
    WARNING    — informational; never changes the verdict on its own.
    """

    CHEATING = "CHEATING"
    INCOMPLETE = "INCOMPLETE"
    WARNING = "WARNING"


@dataclass
class Issue:
    vector: str  # short code, e.g. "ADMITTED_STATEMENT"
    severity: Severity
    message: str  # human-readable explanation
    location: str | None = None  # "file:line" or module name
    evidence: str | None = None  # the offending snippet / detail

    def __str__(self) -> str:
        loc = f" [{self.location}]" if self.location else ""
        return f"{self.severity.value}/{self.vector}{loc}: {self.message}"
