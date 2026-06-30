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

from evaluator.termination import (
    INFRA_RULES,
    TerminationContext,
    TerminationReason,
    claude_code_result_error,
    classify,
    codex_turn_failed,
)

# codex stream cut short by a corrupted/refused request (no turn.completed).
INFRA_STREAM = [
    {"type": "thread.started", "thread_id": "t1"},
    {"type": "turn.started"},
    {"type": "item.completed", "item": {"id": "i0", "type": "command_execution"}},
    {"type": "error", "message": "{\"type\":\"error\",\"error\":{\"type\":\"invalid_request_error\"}}"},
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


def _ctx(path, backend="codex"):
    return TerminationContext(backend=backend, jsonl_path=path)


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


def test_registry_is_the_extension_point():
    # The interface contract: classify() runs INFRA_RULES in order.
    assert codex_turn_failed in INFRA_RULES
    assert claude_code_result_error in INFRA_RULES


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
