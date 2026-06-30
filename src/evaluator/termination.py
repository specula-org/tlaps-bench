"""Classify how an agent run terminated — in particular, whether a benchmark
result is trustworthy or was cut short by INFRA_ERROR.

A benchmark verdict (PASS/FAIL) is a capability signal only if the agent
actually got to make a genuine attempt. When the run is cut short by
infrastructure — a corrupted/refused API request, a dropped stream, a server
overload — the resulting FAIL says nothing about the model. We tag such runs
with ``termination_reason = INFRA_ERROR`` so they can be filtered out (and,
later, auto-retried) instead of being read as genuine failures.

Detection is a registry of RULES (criteria). Each rule inspects a
``TerminationContext`` and returns a reason if it fires, else ``None``; the
first rule that fires wins (see :func:`classify`). Today there is exactly one
rule — :func:`codex_turn_failed`. Add more (other backends, which branch on
``ctx.backend`` and read their own event vocabulary; or other patterns) by
appending to :data:`INFRA_RULES`.

This module only CLASSIFIES. Acting on the classification (e.g. auto-retrying
an INFRA_ERROR run) is intentionally left to the caller.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Callable, Optional


class TerminationReason:
    """How an agent run ended.

    Plain string constants so the value serializes verbatim into results.json.
    Only OK and INFRA_ERROR exist today; extend with e.g. TIMEOUT / USAGE_LIMIT
    as new rules are added — keep the values stable, downstream filters match
    on them.
    """

    OK = "OK"
    INFRA_ERROR = "INFRA_ERROR"


@dataclass
class TerminationContext:
    """The evidence a rule may inspect.

    ``backend`` lets a rule apply only to the backend whose event format it
    understands. ``events()`` lazily parses the agent's JSONL event stream
    (empty list on a missing/unreadable file), so rules that don't need it pay
    nothing. ``agent_exit`` and ``error`` are the runner's already-recorded
    fields, available to rules that key off them instead of the stream.
    """

    backend: str
    jsonl_path: Optional[str]
    agent_exit: Optional[int] = None
    error: str = ""
    _events: Optional[list] = None

    def events(self) -> list:
        if self._events is None:
            self._events = _read_events(self.jsonl_path)
        return self._events


def _read_events(path: Optional[str]) -> list:
    """Parse a JSONL event stream into a list of dicts, tolerantly (skip blank
    and unparseable lines; empty list if the file is absent)."""
    if not path:
        return []
    out: list = []
    try:
        with open(path) as f:
            for raw in f:
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    out.append(json.loads(raw))
                except json.JSONDecodeError:
                    continue
    except FileNotFoundError:
        return []
    return out


# A rule inspects the context and returns a TerminationReason if it fires, else
# None. Rules must be cheap and side-effect free.
Rule = Callable[[TerminationContext], Optional[str]]


def codex_turn_failed(ctx: TerminationContext) -> Optional[str]:
    """codex rule: the run ended on a failed turn rather than a completed one.

    codex emits one ``turn.started`` … ``turn.completed`` per turn. An
    infrastructure error — a corrupted/refused request, a dropped stream, a
    server overload — instead surfaces as ``error`` events and a terminal
    ``turn.failed`` with no following ``turn.completed``. A genuine "I couldn't
    prove it" run, by contrast, ends with ``turn.completed`` (the model ran to
    a normal stop; its proof simply didn't verify).

    We flag INFRA_ERROR when the last terminal turn event is a failure, or when
    the run errored without ever completing a turn. A run that hit a transient
    error mid-way but recovered and completed a turn is NOT flagged.
    """
    if ctx.backend != "codex":
        return None
    last_terminal = None  # "completed" | "failed"
    saw_error = False
    for ev in ctx.events():
        t = ev.get("type")
        if t == "turn.completed":
            last_terminal = "completed"
        elif t == "turn.failed":
            last_terminal = "failed"
        elif t == "error":
            saw_error = True
    if last_terminal == "failed":
        return TerminationReason.INFRA_ERROR
    if last_terminal is None and saw_error:
        return TerminationReason.INFRA_ERROR
    return None


# Registry of INFRA_ERROR criteria. ONE rule today; append more here (rules for
# other backends, or other codex patterns) — classify() returns the first that
# fires. This list IS the extension point.
INFRA_RULES: list[Rule] = [
    codex_turn_failed,
]


def classify(ctx: TerminationContext) -> str:
    """Return the run's TerminationReason: the first INFRA rule that fires, else OK."""
    for rule in INFRA_RULES:
        reason = rule(ctx)
        if reason:
            return reason
    return TerminationReason.OK
