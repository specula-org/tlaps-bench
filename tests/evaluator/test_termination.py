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
    # Same failing stream, but a non-codex backend: the codex rule must abstain,
    # so it classifies OK (until that backend's own rule is added).
    p = _write_jsonl(tmp_path / "infra.jsonl", INFRA_STREAM)
    assert codex_turn_failed(_ctx(p, backend="claude_code")) is None
    assert classify(_ctx(p, backend="claude_code")) == TerminationReason.OK


def test_missing_stream_is_ok(tmp_path):
    # No event file (e.g. agent never launched) must not crash and is not INFRA.
    assert classify(_ctx(str(tmp_path / "nope.jsonl"))) == TerminationReason.OK


def test_registry_is_the_extension_point():
    # The interface contract: classify() runs INFRA_RULES in order. One rule today.
    assert codex_turn_failed in INFRA_RULES
