"""termination.classify — tag a run as INFRA_ERROR vs OK.

A FAIL is only a capability signal if the agent made a genuine attempt. The
codex rule reads the agent's event stream: a run that ends on a terminal
``turn.failed`` (or errors without ever completing a turn) was cut short by
infrastructure — corrupted/refused request, dropped stream, server overload —
and is tagged INFRA_ERROR; a run that ends with ``turn.completed`` is OK
(genuine, even if its proof didn't verify).

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_termination.py
"""

import json
import os

import pytest

from evaluator.backends import get_backend
from evaluator.backends.agentic import AgenticBackend
from evaluator.termination import (
    INFRA_RULES,
    TerminationContext,
    TerminationReason,
    agent_startup_failure,
    classify,
    claude_code_result_error,
    codex_turn_failed,
    copilot_session_error,
    is_wall_clock_timeout,
    one_shot_result_error,
    startup_error_snippet,
)

# codex stream cut short by a corrupted/refused request (no turn.completed).
INFRA_STREAM = [
    {"type": "thread.started", "thread_id": "t1"},
    {"type": "turn.started"},
    {"type": "item.completed", "item": {"id": "i0", "type": "command_execution"}},
    {"type": "error", "message": '{"type":"error","error":{"type":"invalid_request_error"}}'},
    {"type": "turn.failed", "error": {"message": "invalid_request_error"}},
]

# codex stream that ran to a normal stop (proof may still have failed grading).
GENUINE_STREAM = [
    {"type": "thread.started", "thread_id": "t2"},
    {"type": "turn.started"},
    {"type": "item.completed", "item": {"id": "i0", "type": "agent_message", "text": "couldn't finish"}},
    {"type": "turn.completed", "usage": {"input_tokens": 100, "output_tokens": 10}},
]

# transient error mid-run, then recovered and completed → still OK.
RECOVERED_STREAM = [
    {"type": "turn.started"},
    {"type": "error", "message": "Reconnecting... 1/5 (stream disconnected before completion)"},
    {"type": "item.completed", "item": {"id": "i0", "type": "agent_message"}},
    {"type": "turn.completed", "usage": {"input_tokens": 50, "output_tokens": 5}},
]

# stream truncated after errors with no terminal turn event (killed mid-turn).
ERRORED_NO_TURN_STREAM = [
    {"type": "turn.started"},
    {"type": "error", "message": "stream disconnected before completion"},
]


def _write_jsonl(path, events):
    with open(path, "w") as f:
        for e in events:
            f.write(json.dumps(e) + "\n")
    return str(path)


def _ctx(path, backend="codex", agent_exit=None, error="", approach=None, provider=None):
    if approach is None:
        approach = "one_shot" if backend.endswith("_oneshot") else "agentic"
    if provider is None and approach == "one_shot":
        provider = backend.removesuffix("_oneshot")
    validator = (
        get_backend(backend).validate_request_audit if approach == "one_shot" and backend.endswith("_oneshot") else None
    )
    return TerminationContext(
        backend=backend,
        jsonl_path=path,
        approach=approach,
        provider=provider,
        request_audit_validator=validator,
        agent_exit=agent_exit,
        error=error,
    )


def _strict_audit(provider, requests=1, contract_ok=True, **evidence):
    audit = {
        "provider": provider,
        "model_requests": requests,
        "request_attempts": requests,
        "blocked_requests": 0,
        "system_prompt_present": False,
        "tools_present": False,
        "retries_enabled": False,
        "audit_scope": "wire" if provider == "copilot" else "adapter",
        "contract_ok": contract_ok,
    }
    if provider == "copilot":
        audit.update(
            wire_audited=True,
            inference_requests=requests,
            inference_attempts=requests,
            unknown_requests=0,
            system_removed=requests == 1,
            tools_removed=requests == 1,
        )
    else:
        audit.update(
            wire_audited=False,
            litellm_completion_invocations=requests,
            litellm_retries_disabled=True,
            system_supplied=False,
            tools_supplied=False,
        )
    audit.update(evidence)
    return audit


def test_turn_failed_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "infra.jsonl", INFRA_STREAM)
    assert classify(_ctx(p)) == TerminationReason.INFRA_ERROR


def test_turn_completed_is_ok(tmp_path):
    p = _write_jsonl(tmp_path / "genuine.jsonl", GENUINE_STREAM)
    assert classify(_ctx(p)) == TerminationReason.OK


def test_recovered_midrun_error_is_ok(tmp_path):
    p = _write_jsonl(tmp_path / "recovered.jsonl", RECOVERED_STREAM)
    assert classify(_ctx(p)) == TerminationReason.OK


def test_errored_without_completing_a_turn_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "killed.jsonl", ERRORED_NO_TURN_STREAM)
    assert classify(_ctx(p)) == TerminationReason.INFRA_ERROR


def test_rule_only_applies_to_its_backend(tmp_path):
    # The codex rule keys off codex's event vocabulary and must abstain for any
    # other backend; a backend with no rule of its own classifies OK.
    p = _write_jsonl(tmp_path / "infra.jsonl", INFRA_STREAM)
    assert codex_turn_failed(_ctx(p, backend="claude_code")) is None
    assert classify(_ctx(p, backend="litellm")) == TerminationReason.OK


def test_missing_stream_is_ok(tmp_path):
    # No event file (e.g. agent never launched) must not crash and is not INFRA.
    assert classify(_ctx(str(tmp_path / "nope.jsonl"))) == TerminationReason.OK


# --- wall-clock timeout: a LIMIT, consistent across backends, never INFRA -----

# A SIGKILLed run leaves a truncated stream (no terminal turn/result) — exactly
# what each INFRA rule would otherwise read as a cut-off — plus the runner's
# agent_exit == -1 and "<backend> timeout after <N>s" error.
TRUNCATED_BY_BACKEND = {
    "codex": [{"type": "thread.started"}, {"type": "turn.started"}],
    "claude_code": [{"type": "system", "subtype": "init"}, {"type": "assistant", "message": {}}],
    "copilot": [{"type": "assistant.message", "data": {"content": "working"}}],
}


def test_is_wall_clock_timeout_signal():
    ctx = TerminationContext(backend="codex", jsonl_path=None, agent_exit=-1, error="codex timeout after 7200s")
    assert is_wall_clock_timeout(ctx) is True
    # a non-timeout error, or a clean exit, is not a timeout
    assert is_wall_clock_timeout(TerminationContext("codex", None, agent_exit=1, error="")) is False
    assert (
        is_wall_clock_timeout(TerminationContext("codex", None, agent_exit=-1, error="provider usage limit")) is False
    )


def test_timeout_is_timeout_not_infra_for_every_backend(tmp_path):
    # Same wall-clock timeout, every backend → TIMEOUT (not INFRA, not OK) — the
    # truncated stream alone would read as a cut-off, but the timeout wins.
    for backend, stream in TRUNCATED_BY_BACKEND.items():
        p = _write_jsonl(tmp_path / f"{backend}.jsonl", stream)
        err = f"{backend} timeout after 7200s"
        verdict = classify(_ctx(p, backend=backend, agent_exit=-1, error=err))
        assert verdict == TerminationReason.TIMEOUT, f"{backend}: {verdict}"


def test_same_truncation_without_timeout_is_still_infra(tmp_path):
    # Without the timeout signal, a truncated stream is a genuine cut-off (crash /
    # dropped connection) → INFRA_ERROR. Asserts the timeout precheck is the only
    # thing reclassifying these, and only for codex does a clean SIGKILL-less
    # truncation read as OK (no error/turn.failed to key on).
    expected = {
        "codex": TerminationReason.OK,
        "claude_code": TerminationReason.INFRA_ERROR,
        "copilot": TerminationReason.INFRA_ERROR,
    }
    for backend, stream in TRUNCATED_BY_BACKEND.items():
        p = _write_jsonl(tmp_path / f"{backend}.jsonl", stream)
        assert classify(_ctx(p, backend=backend)) == expected[backend], backend


def test_registry_is_the_extension_point():
    # The interface contract: classify() runs INFRA_RULES in order.
    assert codex_turn_failed in INFRA_RULES
    assert claude_code_result_error in INFRA_RULES
    assert copilot_session_error in INFRA_RULES
    assert one_shot_result_error in INFRA_RULES
    assert agent_startup_failure in INFRA_RULES


def test_one_shot_provider_error_is_infra(tmp_path):
    stream = [
        {"type": "request_audit", **_strict_audit("copilot", requests=0)},
        {"type": "error", "message": "authentication failed"},
        {"type": "result", "status": "error", "model_requests": 0},
    ]
    path = _write_jsonl(tmp_path / "oneshot-error.jsonl", stream)
    assert classify(_ctx(path, backend="copilot_oneshot", agent_exit=1)) == TerminationReason.INFRA_ERROR


def test_one_shot_provider_deadline_is_timeout(tmp_path):
    stream = [
        {"type": "usage", "input_tokens": 10, "output_tokens": 4, "model_requests": 1},
        {
            "type": "request_audit",
            **_strict_audit("copilot"),
            "wire_audited": True,
            "inference_requests": 1,
            "inference_attempts": 1,
            "blocked_requests": 0,
            "system_removed": True,
            "tools_removed": True,
        },
        {"type": "error", "message": "Copilot request timed out after 37s"},
        {"type": "result", "status": "timeout", "model_requests": 1},
    ]
    path = _write_jsonl(tmp_path / "oneshot-timeout.jsonl", stream)

    assert classify(_ctx(path, backend="copilot_oneshot", agent_exit=1)) == TerminationReason.TIMEOUT


@pytest.mark.parametrize(
    ("provider", "requests", "contract_ok"),
    [("wrong", 1, True), ("copilot", 2, False), ("copilot", 1, False)],
)
def test_one_shot_provider_deadline_requires_valid_audit(tmp_path, provider, requests, contract_ok):
    stream = [
        {
            "type": "request_audit",
            **_strict_audit(provider, requests=requests, contract_ok=contract_ok),
            "wire_audited": True,
            "inference_requests": requests,
            "inference_attempts": requests,
            "blocked_requests": 0,
            "system_removed": True,
            "tools_removed": True,
        },
        {"type": "result", "status": "timeout", "model_requests": requests},
    ]
    path = _write_jsonl(tmp_path / f"oneshot-invalid-timeout-{provider}-{requests}.jsonl", stream)

    assert classify(_ctx(path, backend="copilot_oneshot", agent_exit=1)) == TerminationReason.INFRA_ERROR


def test_one_shot_deadline_before_request_is_still_timeout(tmp_path):
    stream = [
        {"type": "request_audit", **_strict_audit("copilot", requests=0)},
        {"type": "error", "message": "benchmark deadline reached during startup"},
        {"type": "result", "status": "timeout", "model_requests": 0},
    ]
    path = _write_jsonl(tmp_path / "oneshot-startup-timeout.jsonl", stream)

    assert classify(_ctx(path, backend="copilot_oneshot", agent_exit=1)) == TerminationReason.TIMEOUT


def test_one_shot_clean_response_is_genuine(tmp_path):
    stream = [
        {"type": "response", "text": "not a complete module"},
        {"type": "usage", "input_tokens": 10, "output_tokens": 4, "model_requests": 1},
        {
            "type": "request_audit",
            **_strict_audit("litellm"),
            "litellm_completion_invocations": 1,
            "wire_audited": False,
            "litellm_retries_disabled": True,
            "system_supplied": False,
            "tools_supplied": False,
        },
        {"type": "result", "status": "success", "model_requests": 1},
    ]
    path = _write_jsonl(tmp_path / "oneshot-success.jsonl", stream)
    assert classify(_ctx(path, backend="litellm_oneshot")) == TerminationReason.OK


def test_one_shot_clean_copilot_response_is_genuine(tmp_path):
    stream = [
        {"type": "response", "text": "not a complete module"},
        {
            "type": "request_audit",
            **_strict_audit("copilot"),
            "wire_audited": True,
            "inference_requests": 1,
            "inference_attempts": 1,
            "blocked_requests": 0,
            "system_removed": True,
            "tools_removed": True,
        },
        {"type": "result", "status": "success", "model_requests": 1},
    ]

    path = _write_jsonl(tmp_path / "copilot-oneshot-success.jsonl", stream)
    assert classify(_ctx(path, backend="copilot_oneshot")) == TerminationReason.OK


@pytest.mark.parametrize(
    "backend,audit",
    [
        (
            "litellm_oneshot",
            {
                **_strict_audit("litellm", contract_ok=True),
                "wire_audited": False,
                "litellm_completion_invocations": 1,
                "litellm_retries_disabled": True,
                "system_supplied": True,
                "tools_supplied": False,
            },
        ),
        (
            "copilot_oneshot",
            {
                **_strict_audit("copilot", contract_ok=True),
                "wire_audited": True,
                "inference_requests": 1,
                "inference_attempts": 1,
                "blocked_requests": 0,
                "system_removed": False,
                "tools_removed": True,
            },
        ),
    ],
)
def test_one_shot_context_audit_regression_is_infra(tmp_path, backend, audit):
    stream = [
        {"type": "response", "text": "not a complete module"},
        {"type": "request_audit", **audit},
        {"type": "result", "status": "success", "model_requests": 1},
    ]

    path = _write_jsonl(tmp_path / f"{backend}-context-regression.jsonl", stream)
    assert classify(_ctx(path, backend=backend)) == TerminationReason.INFRA_ERROR


@pytest.mark.parametrize(
    ("backend", "field", "value"),
    [
        ("litellm_oneshot", "model_requests", True),
        ("litellm_oneshot", "request_attempts", 1.0),
        ("litellm_oneshot", "blocked_requests", False),
        ("litellm_oneshot", "litellm_completion_invocations", True),
        ("copilot_oneshot", "model_requests", 1.0),
        ("copilot_oneshot", "request_attempts", True),
        ("copilot_oneshot", "blocked_requests", 0.0),
        ("copilot_oneshot", "inference_requests", True),
        ("copilot_oneshot", "inference_attempts", 1.0),
        ("copilot_oneshot", "unknown_requests", False),
    ],
)
def test_one_shot_audit_counts_require_exact_integers(tmp_path, backend, field, value):
    provider = backend.removesuffix("_oneshot")
    audit = _strict_audit(provider)
    audit[field] = value
    stream = [
        {"type": "response", "text": "candidate"},
        {"type": "request_audit", **audit},
        {"type": "result", "status": "success", "model_requests": 1},
    ]
    path = _write_jsonl(tmp_path / f"{backend}-{field}.jsonl", stream)

    assert classify(_ctx(path, backend=backend)) == TerminationReason.INFRA_ERROR


@pytest.mark.parametrize("field", ["system_removed", "tools_removed"])
def test_copilot_zero_request_audit_requires_explicit_context_evidence(tmp_path, field):
    audit = _strict_audit("copilot", requests=0)
    audit.pop(field)
    stream = [
        {"type": "request_audit", **audit},
        {"type": "result", "status": "timeout", "model_requests": 0},
    ]
    path = _write_jsonl(tmp_path / f"copilot-missing-{field}.jsonl", stream)

    assert classify(_ctx(path, backend="copilot_oneshot")) == TerminationReason.INFRA_ERROR


def test_one_shot_truncated_stream_is_infra(tmp_path):
    path = _write_jsonl(tmp_path / "oneshot-truncated.jsonl", [{"type": "request_audit"}])
    assert classify(_ctx(path, backend="litellm_oneshot")) == TerminationReason.INFRA_ERROR


def test_one_shot_non_utf8_stream_fails_closed(tmp_path):
    path = tmp_path / "oneshot-invalid-utf8.jsonl"
    path.write_bytes(b'{"type":"response","text":"candidate"}\n\xff\n')

    assert classify(_ctx(str(path), backend="litellm_oneshot")) == TerminationReason.INFRA_ERROR


@pytest.mark.parametrize("contents", [None, "", "  \n", "not json\n", "[]\n", "null\n", '"text"\n'])
def test_one_shot_missing_or_corrupt_stream_fails_closed(tmp_path, contents):
    path = tmp_path / "invalid-one-shot.jsonl"
    if contents is not None:
        path.write_text(contents)

    ctx = TerminationContext(
        backend="custom-evaluator",
        jsonl_path=str(path),
        approach="one_shot",
        provider="litellm",
        agent_exit=0,
    )

    assert classify(ctx) == TerminationReason.INFRA_ERROR


def test_one_shot_rejects_junk_mixed_with_valid_contract(tmp_path):
    path = tmp_path / "mixed-one-shot.jsonl"
    valid_events = [
        {"type": "response", "text": "candidate"},
        {"type": "request_audit", **_strict_audit("litellm")},
        {"type": "result", "status": "success", "model_requests": 1},
    ]
    path.write_text("junk\n" + "".join(json.dumps(event) + "\n" for event in valid_events))

    ctx = TerminationContext(
        backend="custom-evaluator",
        jsonl_path=str(path),
        approach="one_shot",
        provider="litellm",
        agent_exit=0,
    )

    assert classify(ctx) == TerminationReason.INFRA_ERROR


@pytest.mark.parametrize("event_type", ["response", "request_audit", "result"])
def test_one_shot_duplicate_contract_event_is_infra(tmp_path, event_type):
    stream = [
        {"type": "response", "text": "not a complete module"},
        {
            "type": "request_audit",
            **_strict_audit("litellm"),
            "litellm_completion_invocations": 1,
            "wire_audited": False,
            "litellm_retries_disabled": True,
            "system_supplied": False,
            "tools_supplied": False,
        },
        {"type": "result", "status": "success", "model_requests": 1},
    ]
    stream.append(next(event.copy() for event in stream if event["type"] == event_type))

    path = _write_jsonl(tmp_path / f"oneshot-duplicate-{event_type}.jsonl", stream)
    assert classify(_ctx(path, backend="litellm_oneshot")) == TerminationReason.INFRA_ERROR


@pytest.mark.parametrize(
    "backend,audit",
    [
        (
            "litellm_oneshot",
            {
                **_strict_audit("litellm", requests=2, contract_ok=False),
                "litellm_completion_invocations": 2,
                "wire_audited": False,
                "litellm_retries_disabled": True,
                "system_supplied": False,
                "tools_supplied": False,
            },
        ),
        (
            "copilot_oneshot",
            {
                **_strict_audit("copilot", requests=2, contract_ok=False),
                "wire_audited": True,
                "inference_requests": 2,
                "inference_attempts": 2,
                "blocked_requests": 0,
            },
        ),
    ],
)
def test_one_shot_success_with_two_requests_is_infra(tmp_path, backend, audit):
    stream = [
        {"type": "response", "text": "not a complete module"},
        {"type": "request_audit", **audit},
        {"type": "result", "status": "success", "model_requests": 2},
    ]

    path = _write_jsonl(tmp_path / f"{backend}-two-requests.jsonl", stream)
    assert classify(_ctx(path, backend=backend)) == TerminationReason.INFRA_ERROR


# --- quota exhaustion: runner-owned, never produced by classify() -----------


def test_quota_exhausted_is_a_distinct_reason():
    # QUOTA_EXHAUSTED is its own category, distinct from OK/INFRA_ERROR/TIMEOUT.
    reasons = {TerminationReason.OK, TerminationReason.INFRA_ERROR, TerminationReason.TIMEOUT}
    assert TerminationReason.QUOTA_EXHAUSTED not in reasons


def test_classify_never_returns_quota_exhausted(tmp_path):
    # The runner sets QUOTA_EXHAUSTED directly (it owns the quota signal); no
    # classify() rule may spontaneously produce it. A quota-blocked run leaves a
    # no-work, truncated stream — classify() reads that as INFRA_ERROR/OK, never
    # QUOTA_EXHAUSTED — which is exactly why the runner tags it before classify().
    for backend, stream in TRUNCATED_BY_BACKEND.items():
        p = _write_jsonl(tmp_path / f"{backend}.jsonl", stream)
        assert classify(_ctx(p, backend=backend)) != TerminationReason.QUOTA_EXHAUSTED


# QUOTA_EXHAUSTED is the one reason the runner sets directly (not classify()), so
# it's only covered by driving run_single_benchmark. Both quota paths short-
# circuit before the AI agent / grader run, so stubbing the quota gate reaches
# them without a real backend, tlapm, or API key.


class _FakeBackend(AgenticBackend):
    name = "codex"

    def build_command(self, workspace, result_dir):
        return ["fake-agent"]

    def parse_output(self, jsonl_path):
        return ("", 0, 0)  # transcript, input_tokens, output_tokens

    def detect_quota_block(self, jsonl_path):
        return None


class _FakeMode:
    name = "proof-completion"

    def __init__(self, bench_dir):
        self._bench_dir = bench_dir

    def benchmark_dir(self):
        return self._bench_dir

    def get_dependencies(self, benchmark_path):
        return []

    def checker_binary_path(self):
        return "/bin/true"

    def build_prompt(self, basename, tlapm_path, tlapm_lib):
        return "prove it"


def _quota_work_item(tmp_path):
    from evaluator.runner import WorkItem

    bench_dir = tmp_path / "bench"
    bench_path = bench_dir / "Foo" / "Bar.tla"
    os.makedirs(bench_path.parent)
    bench_path.write_text("---- MODULE Bar ----\n====\n")
    return WorkItem(
        benchmark_path=str(bench_path),
        output_dir=str(tmp_path / "out"),
        timeout=10,
        check_timeout=10,
        backend=_FakeBackend(),  # ty:ignore[invalid-argument-type]
        mode=_FakeMode(str(bench_dir)),  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        usage_script="dummy",  # enables the quota gate
        quota_max_waits=1,
    )


def test_runner_prerun_quota_skip_tags_quota_exhausted(tmp_path, monkeypatch):
    # Proactive gate gives up before the agent runs (max waits reached): the
    # early return must carry QUOTA_EXHAUSTED, not the seeded OK default.
    from evaluator import runner

    monkeypatch.setattr(runner.quota, "wait_for_quota", lambda *a, **k: False)
    result = runner.run_single_benchmark(_quota_work_item(tmp_path))
    assert result["agent_exit"] == -3
    assert result["termination_reason"] == TerminationReason.QUOTA_EXHAUSTED


def test_runner_duringrun_quota_exhausted_tags_quota_exhausted(tmp_path, monkeypatch):
    # Agent runs, then the provider hard-caps us and the retry budget is spent:
    # run_with_quota_retry returns falsy -> quota_exhausted block (agent never
    # actually invoked, grading skipped).
    from evaluator import runner

    monkeypatch.setattr(runner.quota, "wait_for_quota", lambda *a, **k: True)
    monkeypatch.setattr(runner.quota, "run_with_quota_retry", lambda run, block, **k: False)
    result = runner.run_single_benchmark(_quota_work_item(tmp_path))
    assert result["agent_exit"] == -3
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == TerminationReason.QUOTA_EXHAUSTED


# --- claude_code rule -------------------------------------------------------

# claude_code closes with a `result` event; subtype `success` vs `error_*`.
CC_SUCCESS = [
    {"type": "system", "subtype": "init"},
    {"type": "assistant", "message": {"role": "assistant"}},
    {"type": "result", "subtype": "success", "is_error": False, "result": "done"},
]
CC_EXEC_ERROR = [
    {"type": "system", "subtype": "init"},
    {"type": "result", "subtype": "error_during_execution", "is_error": True},
]
CC_MAX_TURNS = [
    {"type": "system", "subtype": "init"},
    {"type": "result", "subtype": "error_max_turns", "is_error": True},
]
CC_TRUNCATED = [  # stream cut off before the terminal result event
    {"type": "system", "subtype": "init"},
    {"type": "assistant", "message": {"role": "assistant"}},
]


def test_cc_success_is_ok(tmp_path):
    p = _write_jsonl(tmp_path / "ok.jsonl", CC_SUCCESS)
    assert classify(_ctx(p, backend="claude_code")) == TerminationReason.OK


def test_cc_exec_error_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "err.jsonl", CC_EXEC_ERROR)
    assert classify(_ctx(p, backend="claude_code")) == TerminationReason.INFRA_ERROR


def test_cc_max_turns_is_not_infra(tmp_path):
    # error_max_turns is a turn-budget LIMIT, not infrastructure — must NOT flag.
    p = _write_jsonl(tmp_path / "maxturns.jsonl", CC_MAX_TURNS)
    assert classify(_ctx(p, backend="claude_code")) == TerminationReason.OK


def test_cc_truncated_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "trunc.jsonl", CC_TRUNCATED)
    assert classify(_ctx(p, backend="claude_code")) == TerminationReason.INFRA_ERROR


def test_cc_rule_only_applies_to_claude_code(tmp_path):
    # codex stream through the claude rule must abstain.
    p = _write_jsonl(tmp_path / "infra.jsonl", INFRA_STREAM)
    assert claude_code_result_error(_ctx(p, backend="codex")) is None


# --- copilot rule (event vocabulary per Copilot SDK streaming-events docs) ---

# A clean run: per-tool failure is normal (tlapm rejecting a proof), terminal
# `result` with a non-zero exitCode is the proof failing — neither is infra.
CP_COMPLETED = [
    {"type": "assistant.message", "data": {"content": "hi"}},
    {"type": "tool.execution_complete", "data": {"result": {"success": False}}},
    {"type": "result", "exitCode": 1, "usage": {"premiumRequests": 1}},
]
CP_SESSION_ERROR = [  # dedicated infra error event (auth/quota/network)
    {"type": "assistant.message", "data": {"content": "hi"}},
    {"type": "session.error", "errorType": "quota", "message": "rate limited", "statusCode": 429},
]
CP_ABORT = [
    {"type": "assistant.message", "data": {"content": "hi"}},
    {"type": "abort"},
]
CP_SHUTDOWN_ERROR = [
    {"type": "session.shutdown", "shutdownType": "error", "errorReason": "stream closed"},
]
CP_SHUTDOWN_OK = [
    {"type": "session.shutdown", "shutdownType": "routine"},
]
CP_RECOVERED = [  # intermittent session.error, then recovered to a clean terminal
    {"type": "assistant.message", "data": {"content": "hi"}},
    {"type": "session.error", "errorType": "quota", "message": "transient 429"},
    {"type": "assistant.message", "data": {"content": "retrying"}},
    {"type": "result", "exitCode": 0, "usage": {"premiumRequests": 2}},
]
CP_TRUNCATED = [  # cut off before any terminal event
    {"type": "assistant.message", "data": {"content": "working"}},
    {"type": "tool.execution_start", "data": {}},
]


def test_copilot_completed_is_ok(tmp_path):
    p = _write_jsonl(tmp_path / "done.jsonl", CP_COMPLETED)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.OK


def test_copilot_session_error_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "serr.jsonl", CP_SESSION_ERROR)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.INFRA_ERROR


def test_copilot_abort_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "abort.jsonl", CP_ABORT)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.INFRA_ERROR


def test_copilot_shutdown_error_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "sd.jsonl", CP_SHUTDOWN_ERROR)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.INFRA_ERROR


def test_copilot_shutdown_routine_is_ok(tmp_path):
    p = _write_jsonl(tmp_path / "sdok.jsonl", CP_SHUTDOWN_OK)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.OK


def test_copilot_recovered_session_error_is_ok(tmp_path):
    # Only a WHOLESALE failure counts: a session.error the run recovered from
    # (followed by a clean terminal) must NOT be flagged.
    p = _write_jsonl(tmp_path / "recov.jsonl", CP_RECOVERED)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.OK


def test_copilot_truncated_is_infra(tmp_path):
    p = _write_jsonl(tmp_path / "trunc.jsonl", CP_TRUNCATED)
    assert classify(_ctx(p, backend="copilot")) == TerminationReason.INFRA_ERROR


def test_copilot_rule_only_applies_to_copilot(tmp_path):
    p = _write_jsonl(tmp_path / "trunc.jsonl", CP_TRUNCATED)
    assert copilot_session_error(_ctx(p, backend="codex")) is None


# --- backend-independent startup rule (empty stream + nonzero exit) ----------

# The observed Copilot startup failures: a 0-byte output.jsonl, agent_exit 1,
# and the real error only in stderr, wrapped in install/firewall noise.
COPILOT_STARTUP_STDERR = """\
added 3 packages in 8s
[firewall] Allowed: api.githubcopilot.com -> 140.82.113.22
Error: Failed to load models

Error: Failed to list models
"""


def _startup_ctx(tmp_path, stderr=None, backend="copilot", agent_exit=1, error=""):
    # A 0-byte event stream, exactly as the observed startup failures left it.
    jsonl = tmp_path / "output.jsonl"
    jsonl.write_text("")
    stderr_path = None
    if stderr is not None:
        p = tmp_path / "stderr.txt"
        p.write_text(stderr)
        stderr_path = str(p)
    return TerminationContext(
        backend=backend, jsonl_path=str(jsonl), agent_exit=agent_exit, error=error, stderr_path=stderr_path
    )


def test_startup_failure_is_infra_for_every_backend(tmp_path):
    # The rule keys on the failure's shape, not a backend's event vocabulary.
    for backend in ("copilot", "codex", "claude_code", "litellm"):
        ctx = _startup_ctx(tmp_path, COPILOT_STARTUP_STDERR, backend=backend)
        assert classify(ctx) == TerminationReason.INFRA_ERROR, backend


def test_startup_error_snippet_quotes_the_real_error(tmp_path):
    # The label is the actual error line from stderr (first line mentioning
    # "error"), skipping the npm/firewall noise around it — no hardcoded
    # signature list to go stale.
    assert startup_error_snippet(_startup_ctx(tmp_path, COPILOT_STARTUP_STDERR)) == "Error: Failed to load models"
    dns_stderr = "[firewall] ERROR: no IPs resolved for host 'q.eu-central-1.amazonaws.com'"
    assert startup_error_snippet(_startup_ctx(tmp_path, dns_stderr)) == dns_stderr
    # No "error" wording anywhere: fall back to the last non-empty line.
    assert (
        startup_error_snippet(_startup_ctx(tmp_path, "added 3 packages in 8s\nAuthentication token rejected\n"))
        == "Authentication token rejected"
    )
    assert startup_error_snippet(_startup_ctx(tmp_path, None)) == "no stderr"


def test_reworded_startup_error_is_still_infra(tmp_path):
    # The snippet labels, it never gates: a reworded CLI error must not
    # silently turn startup failures back into proof FAILs.
    ctx = _startup_ctx(tmp_path, "models are having a bad day\n")
    assert classify(ctx) == TerminationReason.INFRA_ERROR
    assert startup_error_snippet(ctx) == "models are having a bad day"


def test_startup_failure_without_stderr_is_still_infra(tmp_path):
    # No stderr dump at all (e.g. the container died before writing one).
    assert classify(_startup_ctx(tmp_path, None)) == TerminationReason.INFRA_ERROR


def test_clean_exit_with_empty_stream_is_not_startup_failure(tmp_path):
    assert classify(_startup_ctx(tmp_path, COPILOT_STARTUP_STDERR, agent_exit=0)) == TerminationReason.OK


def test_startup_rule_never_overrides_timeout(tmp_path):
    # A SIGKILLed run can also leave an empty stream + nonzero exit; the
    # wall-clock timeout precheck must win.
    ctx = _startup_ctx(tmp_path, None, agent_exit=-1, error="copilot timeout after 300s")
    assert classify(ctx) == TerminationReason.TIMEOUT


def test_noisy_stderr_on_clean_run_is_ok(tmp_path):
    # install/firewall noise on stderr is normal — a run that reached a clean
    # terminal event stays OK regardless of what stderr says.
    p = _write_jsonl(tmp_path / "done.jsonl", CP_COMPLETED)
    sp = tmp_path / "stderr.txt"
    sp.write_text(COPILOT_STARTUP_STDERR)  # worst case: even a scary stderr
    ctx = TerminationContext(backend="copilot", jsonl_path=p, agent_exit=0, stderr_path=str(sp))
    assert classify(ctx) == TerminationReason.OK
