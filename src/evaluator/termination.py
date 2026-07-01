"""Classify how an agent run terminated — in particular, whether a benchmark
result is trustworthy or was cut short by INFRA_ERROR.

A benchmark verdict (PASS/FAIL) is a capability signal only if the agent
actually got to make a genuine attempt. When the run is cut short by
infrastructure — a corrupted/refused API request, a dropped stream, a server
overload — the resulting FAIL says nothing about the model. We tag such runs
with ``termination_reason = INFRA_ERROR`` so they can be filtered out (and,
later, auto-retried) instead of being read as genuine failures.

:func:`classify` first checks for a wall-clock timeout (a backend-independent
LIMIT — the model was working, it just ran out of time — reported as TIMEOUT,
never INFRA_ERROR), then runs a registry of INFRA RULES (criteria). Each rule
inspects a ``TerminationContext`` and returns a reason if it fires, else
``None``; the first that fires wins. There is one rule per backend today
(:func:`codex_turn_failed`, :func:`claude_code_result_error`,
:func:`copilot_session_error`), each branching on ``ctx.backend`` to read its
own event vocabulary. Add more by appending to :data:`INFRA_RULES`.

This module only CLASSIFIES. Acting on the classification (e.g. auto-retrying
an INFRA_ERROR run) is intentionally left to the caller.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass


class TerminationReason:
    """How an agent run ended.

    Plain string constants so the value serializes verbatim into results.json.
    Extend with e.g. USAGE_LIMIT as new rules are added — keep the values
    stable, downstream filters match on them.
    """

    OK = "OK"
    INFRA_ERROR = "INFRA_ERROR"
    # The runner SIGKILLed the agent for exceeding its wall-clock budget: a time
    # LIMIT (the model was working), NOT infrastructure. Detected the same way
    # for every backend so they agree (see is_wall_clock_timeout / classify).
    TIMEOUT = "TIMEOUT"
    # A provider hard usage cap stopped the run — the proactive gate exhausted
    # its waits, or the reactive retry gave up. The agent did no genuine work;
    # the run is retriable once the quota window resets. Backend-independent, so
    # every backend agrees. Set directly by the runner (which owns the quota
    # signal), not by a classify() rule — distinct from INFRA_ERROR (retry
    # immediately) and TIMEOUT (out of time).
    QUOTA_EXHAUSTED = "QUOTA_EXHAUSTED"


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
    jsonl_path: str | None
    agent_exit: int | None = None
    error: str = ""
    _events: list | None = None

    def events(self) -> list:
        if self._events is None:
            self._events = _read_events(self.jsonl_path)
        return self._events


def _read_events(path: str | None) -> list:
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
Rule = Callable[[TerminationContext], str | None]


def codex_turn_failed(ctx: TerminationContext) -> str | None:
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


def claude_code_result_error(ctx: TerminationContext) -> str | None:
    """claude_code rule: the run ended on an execution error (or never emitted a
    terminal result at all).

    Claude Code closes a run with one ``type == "result"`` event whose
    ``subtype`` is ``success`` on a clean finish, or an ``error_*`` value
    otherwise (observed: ``error_during_execution``). We flag INFRA_ERROR for
    such an execution error, or when the stream has events but no terminal
    ``result`` (cut off mid-run). ``error_max_turns`` — the agent exhausting its
    turn budget — is a LIMIT, not infrastructure, so it is NOT flagged here.
    """
    if ctx.backend != "claude_code":
        return None
    events = ctx.events()
    if not events:
        return None
    last_result = None
    for ev in events:
        if ev.get("type") == "result":
            last_result = ev
    if last_result is None:
        # Had a stream but no terminal result event: cut off mid-run.
        return TerminationReason.INFRA_ERROR
    subtype = last_result.get("subtype", "")
    if subtype.startswith("error") and subtype != "error_max_turns":
        return TerminationReason.INFRA_ERROR
    return None


def copilot_session_error(ctx: TerminationContext) -> str | None:
    """copilot rule: the run did not reach a clean terminal.

    The GitHub Copilot CLI ends a clean run with a terminal event — ``result``
    (carrying ``exitCode``) on the stdout JSON stream, or ``session.shutdown``
    with ``shutdownType: "routine"``. Infrastructure problems surface as a
    ``session.error`` event (``errorType`` e.g. ``"authentication"`` /
    ``"quota"``), an ``abort``, or ``session.shutdown`` with
    ``shutdownType == "error"``.

    We flag INFRA_ERROR only on a WHOLESALE failure — the run reached no clean
    terminal event. An intermittent ``session.error`` the agent then recovered
    from (followed by a clean terminal) is NOT flagged. A per-tool failure
    (``tool.execution_complete`` with ``success: false`` — e.g. tlapm rejecting
    a proof) and a non-zero ``result`` ``exitCode`` (the proof simply not
    verifying) are normal parts of an attempt and never count. (Event vocabulary
    per the Copilot SDK streaming-events docs; no recorded copilot runs yet to
    validate against.)
    """
    if ctx.backend != "copilot":
        return None
    events = ctx.events()
    if not events:
        return None
    reached_clean_terminal = False
    for ev in events:
        t = ev.get("type")
        if t == "result" or (t == "session.shutdown" and ev.get("shutdownType") != "error"):
            reached_clean_terminal = True
    if reached_clean_terminal:
        return None
    return TerminationReason.INFRA_ERROR


# Registry of INFRA_ERROR criteria. One rule per backend today; append more here
# (other backends, or additional patterns for an existing one) — classify()
# returns the first that fires. This list IS the extension point.
INFRA_RULES: list[Rule] = [
    codex_turn_failed,
    claude_code_result_error,
    copilot_session_error,
]


def is_wall_clock_timeout(ctx: TerminationContext) -> bool:
    """Whether the runner SIGKILLed the agent for exceeding its wall-clock budget.

    The runner records this identically for every backend — ``agent_exit == -1``
    and ``error`` = ``"<backend> timeout after <N>s"`` — so the check is backend
    independent. This is a time LIMIT, not infrastructure: the model was working,
    it just didn't finish in the budget (TLAPS proofs are slow, so timeouts are
    common). A SIGKILL also leaves a truncated event stream — no terminal turn /
    result — which the per-backend INFRA rules would otherwise read as a cut-off;
    classify() checks this first so a timeout is never mislabeled INFRA_ERROR.
    """
    return ctx.agent_exit == -1 and "timeout after" in (ctx.error or "")


def classify(ctx: TerminationContext) -> str:
    """Return the run's TerminationReason.

    A wall-clock timeout (a LIMIT, backend-independent) takes precedence over the
    per-backend INFRA rules, so every backend agrees on it; otherwise the first
    INFRA rule that fires wins, else OK.
    """
    if is_wall_clock_timeout(ctx):
        return TerminationReason.TIMEOUT
    for rule in INFRA_RULES:
        reason = rule(ctx)
        if reason:
            return reason
    return TerminationReason.OK
