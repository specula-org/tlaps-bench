"""Classify how an agent run terminated — in particular, whether a benchmark
result is trustworthy or was cut short by INFRA_ERROR.

A benchmark verdict (PASS/FAIL) is a capability signal only if the agent
actually got to make a genuine attempt. When the run is cut short by
infrastructure — a corrupted/refused API request, a dropped stream, a server
overload — the resulting FAIL says nothing about the model. We tag such runs
with ``termination_reason = INFRA_ERROR`` so they can be filtered out (and
auto-retried by the runner when the model did no work) instead of being read
as genuine failures.

:func:`classify` first checks for a wall-clock timeout (a backend-independent
LIMIT — the model was working, it just ran out of time — reported as TIMEOUT,
never INFRA_ERROR), then runs a registry of INFRA RULES (criteria). Each rule
inspects a ``TerminationContext`` and returns a reason if it fires, else
``None``; the first that fires wins. There is one rule per backend
(:func:`codex_turn_failed`, :func:`claude_code_result_error`,
:func:`copilot_session_error`), each branching on ``ctx.backend`` to read its
own event vocabulary, plus one backend-independent startup rule
(:func:`agent_startup_failure`) for the CLI dying before emitting a single
event. Add more by appending to :data:`INFRA_RULES`.

This module only CLASSIFIES. Acting on the classification (the runner auto-
retries an INFRA_ERROR run whose model did no work) is left to the caller.
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
    ``stderr()`` lazily reads the agent's stderr dump ("" when absent), where a
    startup failure often leaves its only evidence.
    """

    backend: str
    jsonl_path: str | None
    agent_exit: int | None = None
    error: str = ""
    stderr_path: str | None = None
    _events: list | None = None
    _stderr: str | None = None

    def events(self) -> list:
        if self._events is None:
            self._events = _read_events(self.jsonl_path)
        return self._events

    def stderr(self) -> str:
        if self._stderr is None:
            self._stderr = _read_text(self.stderr_path)
        return self._stderr


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


def _read_text(path: str | None) -> str:
    """Contents of a text file, tolerantly ("" when unset/absent/unreadable)."""
    if not path:
        return ""
    try:
        with open(path) as f:
            return f.read()
    except OSError:
        return ""


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


def one_shot_result_error(ctx: TerminationContext) -> str | None:
    """One-shot rule: require one response, audit, and clean provider result.

    The shared one-shot driver emits a terminal ``result`` event. Provider,
    authentication, transport, or request-guard failures end with
    ``status == "error"`` and no complete response; grading the untouched
    ``PROOF OBVIOUS`` file would misreport that infrastructure failure as a
    model capability failure.

    A clean response whose text is not a complete TLA+ module remains a genuine
    attempt: the runner records the materialization failure as FAIL without
    grading the untouched placeholder.
    """
    if not ctx.backend.endswith("_oneshot"):
        return None
    events = ctx.events()
    if not events:
        return None
    responses = [event for event in events if event.get("type") == "response"]
    audits = [event for event in events if event.get("type") == "request_audit"]
    results = [event for event in events if event.get("type") == "result"]
    if len(responses) != 1 or len(audits) != 1 or len(results) != 1:
        return TerminationReason.INFRA_ERROR

    def is_count(value: object, expected: int) -> bool:
        return isinstance(value, int) and not isinstance(value, bool) and value == expected

    terminal = results[0]
    if terminal.get("status") != "success" or not is_count(terminal.get("model_requests"), 1):
        return TerminationReason.INFRA_ERROR
    audit = audits[0]
    provider = ctx.backend.removesuffix("_oneshot")
    if audit.get("provider") != provider:
        return TerminationReason.INFRA_ERROR
    if provider == "copilot" and not (
        audit.get("wire_audited") is True
        and is_count(audit.get("inference_requests"), 1)
        and is_count(audit.get("inference_attempts"), 1)
        and is_count(audit.get("blocked_requests"), 0)
        and audit.get("system_removed") is True
        and audit.get("tools_removed") is True
    ):
        return TerminationReason.INFRA_ERROR
    if provider == "litellm" and not (
        audit.get("wire_audited") is False
        and is_count(audit.get("litellm_completion_invocations"), 1)
        and audit.get("litellm_retries_disabled") is True
        and audit.get("system_supplied") is False
        and audit.get("tools_supplied") is False
    ):
        return TerminationReason.INFRA_ERROR
    return None


def agent_startup_failure(ctx: TerminationContext) -> str | None:
    """Backend-independent rule: the CLI died before emitting a single event
    (observed on Copilot: transient model-list/auth/DNS startup failures with a
    0-byte stream, nonzero exit, and the error only on stderr). Keys on that
    shape alone — never on the stderr wording — covering the per-backend rules'
    empty-stream blind spot for every backend. A wall-clock timeout leaves the
    same shape; classify() checks it first.
    """
    if ctx.events():
        return None
    if not ctx.agent_exit:  # 0 or None: clean/unknown exit, not a startup death
        return None
    return TerminationReason.INFRA_ERROR


def startup_error_snippet(ctx: TerminationContext) -> str:
    """Label for ``infra_retry_reasons``: the first stderr line mentioning
    "error", else the last non-empty line. Diagnostic only — never gates a retry."""
    lines = [ln.strip() for ln in ctx.stderr().splitlines() if ln.strip()]
    if not lines:
        return "no stderr"
    return next((ln for ln in lines if "error" in ln.lower()), lines[-1])[:120]


# Registry of INFRA_ERROR criteria. One rule per backend, then the backend-
# independent startup rule as fallback; append more here (other backends, or
# additional patterns for an existing one) — classify() returns the first that
# fires. This list IS the extension point.
INFRA_RULES: list[Rule] = [
    codex_turn_failed,
    claude_code_result_error,
    copilot_session_error,
    one_shot_result_error,
    agent_startup_failure,
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
