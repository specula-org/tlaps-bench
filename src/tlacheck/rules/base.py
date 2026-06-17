"""Rule protocol: a rule maps a CheckContext to a list of Issues."""

from __future__ import annotations

from typing import Protocol

from ..context import CheckContext
from ..issue import Issue


class Rule(Protocol):
    name: str

    def check(self, ctx: CheckContext) -> list[Issue]: ...
