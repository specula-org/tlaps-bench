"""Claude Code stream-json usage and native USD cost parsing."""

from __future__ import annotations

import json
from pathlib import Path

from evaluator.backends.claude_code import ClaudeCodeBackend, parse_claude_code_usage


def _assistant(
    *,
    input_tokens: int | None = None,
    output_tokens: int | None = None,
    cache_read: int | None = None,
    cache_write: int | None = None,
    model: str = "claude-opus-4-8",
    message_id: str = "msg_1",
    stop_reason: str | None = "end_turn",
) -> dict[str, object]:
    usage: dict[str, object] = {}
    if input_tokens is not None:
        usage["input_tokens"] = input_tokens
    if output_tokens is not None:
        usage["output_tokens"] = output_tokens
    if cache_read is not None:
        usage["cache_read_input_tokens"] = cache_read
    if cache_write is not None:
        usage["cache_creation_input_tokens"] = cache_write
    return {
        "type": "assistant",
        "message": {
            "id": message_id,
            "model": model,
            "stop_reason": stop_reason,
            "content": [{"type": "text", "text": "working"}],
            "usage": usage,
        },
    }


def _result(
    *,
    input_tokens: int | None = None,
    output_tokens: int | None = None,
    cache_read: int | None = None,
    cache_write: int | None = None,
    total_cost_usd: float | None = None,
    duration_api_ms: int | None = None,
    is_error: bool = False,
    subtype: str = "success",
    num_turns: int | None = None,
) -> dict[str, object]:
    usage: dict[str, object] = {}
    if input_tokens is not None:
        usage["input_tokens"] = input_tokens
    if output_tokens is not None:
        usage["output_tokens"] = output_tokens
    if cache_read is not None:
        usage["cache_read_input_tokens"] = cache_read
    if cache_write is not None:
        usage["cache_creation_input_tokens"] = cache_write
    event: dict[str, object] = {
        "type": "result",
        "subtype": subtype,
        "is_error": is_error,
        "result": "done",
        "usage": usage,
    }
    if total_cost_usd is not None:
        event["total_cost_usd"] = total_cost_usd
    if duration_api_ms is not None:
        event["duration_api_ms"] = duration_api_ms
    if num_turns is not None:
        event["num_turns"] = num_turns
    return event


def _write(path: Path, *events: dict[str, object]) -> str:
    path.write_text("".join(json.dumps(event) + "\n" for event in events))
    return str(path)


def test_cache_tokens_classify_input_without_double_counting(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10, cache_read=40, cache_write=20),
        _result(
            input_tokens=100,
            output_tokens=10,
            cache_read=40,
            cache_write=20,
            total_cost_usd=0.0125,
            duration_api_ms=2500,
        ),
    )

    usage = parse_claude_code_usage(path, requested_model="claude-opus-4-8")

    assert usage is not None
    # Anthropic reports cache buckets beside input_tokens; the shared contract
    # folds them in exactly once (100 + 40 + 20).
    assert usage.input_tokens == 160
    assert usage.output_tokens == 10
    assert usage.cache_read_input_tokens == 40
    assert usage.cache_write_input_tokens == 20
    assert usage.model_requests == 1
    assert usage.model_time_secs == 2.5
    assert usage.status == "complete"
    assert usage.costs == tuple(usage.costs)
    assert [cost.to_dict() for cost in usage.costs] == [
        {"amount": 0.0125, "unit": "usd", "source": "claude_code.total_cost_usd"}
    ]


def test_native_usd_cost_is_recorded_in_its_own_unit(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=10, output_tokens=5),
        _result(input_tokens=10, output_tokens=5, total_cost_usd=0.42),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert [cost.to_dict() for cost in usage.costs] == [
        {"amount": 0.42, "unit": "usd", "source": "claude_code.total_cost_usd"}
    ]


def test_per_request_evidence_is_preserved(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10, message_id="msg_a", stop_reason="tool_use"),
        _assistant(input_tokens=60, output_tokens=20, message_id="msg_b", stop_reason="end_turn"),
        _result(input_tokens=160, output_tokens=30, total_cost_usd=0.01),
    )

    usage = parse_claude_code_usage(path, requested_model="claude-opus-4-8")

    assert usage is not None
    assert usage.model_requests == 2
    assert [request.request_id for request in usage.requests] == ["msg_a", "msg_b"]
    assert [request.finish_reasons for request in usage.requests] == [("tool_use",), ("end_turn",)]
    assert usage.requests[0].requested_model == "claude-opus-4-8"
    assert usage.requests[0].provider == "anthropic"
    assert usage.status == "complete"


def test_summary_mismatch_against_messages_is_a_lower_bound(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10),
        _result(input_tokens=999, output_tokens=10, total_cost_usd=0.01),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.status == "lower_bound"
    assert any("result total 999" in warning for warning in usage.warnings)


def test_missing_result_event_is_a_lower_bound(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.status == "lower_bound"
    assert usage.input_tokens == 100
    assert any("result event missing" in warning for warning in usage.warnings)


def test_error_result_is_not_complete(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10),
        _result(input_tokens=100, output_tokens=10, total_cost_usd=0.01, is_error=True, subtype="error"),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.status == "lower_bound"


def test_missing_cost_is_flagged_rather_than_assumed_zero(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10),
        _result(input_tokens=100, output_tokens=10),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.costs == ()
    assert usage.status != "complete"
    assert any("total_cost_usd" in warning for warning in usage.warnings)


def test_unreported_tokens_stay_null_not_zero(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(output_tokens=10),
        _result(output_tokens=10, total_cost_usd=0.01),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.input_tokens is None
    assert usage.to_dict()["input_tokens"] is None
    assert usage.output_tokens == 10


def test_explicit_zero_stays_an_exact_zero(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=0, output_tokens=0),
        _result(input_tokens=0, output_tokens=0, total_cost_usd=0.0),
    )

    usage = parse_claude_code_usage(path)

    assert usage is not None
    assert usage.input_tokens == 0
    assert usage.output_tokens == 0
    assert usage.status == "complete"


def test_backend_falls_back_to_legacy_tokens_when_events_are_absent(tmp_path):
    backend = ClaudeCodeBackend(model="claude-opus-4-8")
    path = str(tmp_path / "missing.jsonl")

    usage = backend.parse_usage(path, input_tokens=12, output_tokens=3)

    assert usage.input_tokens == 12
    assert usage.output_tokens == 3
    assert usage.status == "lower_bound"


def test_backend_reports_unavailable_when_nothing_was_produced(tmp_path):
    backend = ClaudeCodeBackend(model="claude-opus-4-8")
    path = str(tmp_path / "missing.jsonl")

    usage = backend.parse_usage(path, input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None


def test_streamed_partial_output_does_not_falsely_flag_a_complete_run(tmp_path):
    """Regression for a real multi-turn run: each streamed assistant
    output_tokens is a message-start partial that sums well below the settled
    total in the result event (24 vs 673 across six turns). The output total
    must come from the result event, and the streamed output must never drive a
    false lower bound."""

    path = _write(
        tmp_path / "output.jsonl",
        # Six turns; input/cache are exact per message, output is a partial.
        _assistant(input_tokens=10, output_tokens=3, cache_read=14364, cache_write=7163, message_id="m0"),
        _assistant(input_tokens=5, output_tokens=4, cache_read=18674, cache_write=2799, message_id="m1"),
        _assistant(input_tokens=5, output_tokens=4, cache_read=21473, cache_write=225, message_id="m2"),
        _assistant(input_tokens=5, output_tokens=4, cache_read=21698, cache_write=116, message_id="m3"),
        _assistant(input_tokens=6, output_tokens=4, cache_read=21814, cache_write=95, message_id="m4"),
        _assistant(input_tokens=5, output_tokens=5, cache_read=21909, cache_write=190, message_id="m5"),
        _result(
            input_tokens=36,
            output_tokens=673,
            cache_read=119932,
            cache_write=10588,
            total_cost_usd=0.0372752,
            duration_api_ms=8000,
            num_turns=6,
        ),
    )

    usage = parse_claude_code_usage(path, requested_model="claude-haiku-4-5")

    assert usage is not None
    assert usage.status == "complete"
    assert usage.warnings == ()
    # Settled output total from the result event, not the summed partials (24).
    assert usage.output_tokens == 673
    assert usage.input_tokens == 36 + 119932 + 10588
    assert usage.model_requests == 6
    # Per-request output is unknown on success, so it is null rather than the
    # misleading streamed partial; the settled total lives on the summary.
    assert [request.output_tokens for request in usage.requests] == [None] * 6
    assert [request.request_id for request in usage.requests] == ["m0", "m1", "m2", "m3", "m4", "m5"]
    assert [cost.to_dict() for cost in usage.costs] == [
        {"amount": 0.0372752, "unit": "usd", "source": "claude_code.total_cost_usd"}
    ]


def test_per_request_input_and_cache_evidence_is_preserved_on_success(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=10, cache_read=14364, cache_write=7266, output_tokens=1, message_id="m0"),
        _assistant(input_tokens=5, cache_read=18674, cache_write=2799, output_tokens=1, message_id="m1"),
        _result(input_tokens=15, output_tokens=90, cache_read=33038, cache_write=10065, total_cost_usd=0.02),
    )

    usage = parse_claude_code_usage(path, requested_model="claude-haiku-4-5")

    assert usage.status == "complete"
    # Input/cache are final per message and are kept as per-request evidence.
    assert [request.input_tokens for request in usage.requests] == [10 + 14364 + 7266, 5 + 18674 + 2799]
    assert [request.cache_read_input_tokens for request in usage.requests] == [14364, 18674]
    assert usage.output_tokens == 90


def test_streamed_input_mismatch_against_result_is_a_lower_bound(tmp_path):
    """Input/cache are reliable per message, so a mismatch means lost turns."""

    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=1, message_id="m0"),
        _result(input_tokens=999, output_tokens=250, total_cost_usd=0.01),
    )

    usage = parse_claude_code_usage(path)

    assert usage.status == "lower_bound"
    assert any("input_tokens result total 999" in warning for warning in usage.warnings)


def test_model_requests_falls_back_to_num_turns_without_streamed_events(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _result(input_tokens=30, output_tokens=90, total_cost_usd=0.02, num_turns=4),
    )

    usage = parse_claude_code_usage(path)

    assert usage.status == "complete"
    assert usage.model_requests == 4
    assert usage.output_tokens == 90


def _assistant_block(message_id: str, usage: dict[str, int], *, block_index: int) -> dict[str, object]:
    """One content-block event of a multi-block turn, echoing the turn usage."""

    return {
        "type": "assistant",
        "message": {
            "id": message_id,
            "model": "claude-haiku-4-5",
            "stop_reason": "tool_use",
            "content": [{"type": "tool_use", "name": f"Bash{block_index}", "input": {}}],
            "usage": usage,
        },
    }


def test_multi_block_turn_is_counted_once_per_message(tmp_path):
    """Claude Code repeats a turn's usage on every content-block event.

    Regression for a real run where 149 block-events across 94 messages
    inflated the input total by ~1.55x. Each message id must count once.
    """

    turn_usage = {
        "input_tokens": 20121,
        "cache_creation_input_tokens": 7310,
        "cache_read_input_tokens": 12802,
        "output_tokens": 4,
    }
    path = _write(
        tmp_path / "output.jsonl",
        _assistant_block("msg_1", turn_usage, block_index=0),
        _assistant_block("msg_1", turn_usage, block_index=1),
        _assistant_block("msg_1", turn_usage, block_index=2),
        _assistant_block("msg_2", {"input_tokens": 6, "output_tokens": 1}, block_index=0),
        _assistant_block("msg_2", {"input_tokens": 6, "output_tokens": 1}, block_index=1),
    )

    usage = parse_claude_code_usage(path, requested_model="claude-haiku-4-5")

    assert usage is not None
    assert usage.model_requests == 2
    # msg_1: 20121 + 7310 + 12802 = 40233 input; msg_2: 6. Not multiplied by blocks.
    assert usage.input_tokens == 40233 + 6
    assert usage.output_tokens == 4 + 1
    assert [request.request_id for request in usage.requests] == ["msg_1", "msg_2"]


def test_legacy_parse_output_dedupes_multi_block_turns(tmp_path):
    """The legacy fallback total must dedupe the same way as the structured one."""

    turn_usage = {"input_tokens": 100, "cache_read_input_tokens": 40, "output_tokens": 10}
    backend = ClaudeCodeBackend(model="claude-haiku-4-5")
    path = _write(
        tmp_path / "output.jsonl",
        _assistant_block("msg_1", turn_usage, block_index=0),
        _assistant_block("msg_1", turn_usage, block_index=1),
    )

    _, legacy_in, legacy_out = backend.parse_output(path)

    assert (legacy_in, legacy_out) == (140, 10)


def test_legacy_parse_output_total_matches_structured_input_total(tmp_path):
    """The structured record must not change the legacy top-level numbers."""

    backend = ClaudeCodeBackend(model="claude-opus-4-8")
    path = _write(
        tmp_path / "output.jsonl",
        _assistant(input_tokens=100, output_tokens=10, cache_read=40, cache_write=20),
        _result(
            input_tokens=100,
            output_tokens=10,
            cache_read=40,
            cache_write=20,
            total_cost_usd=0.01,
        ),
    )

    _, legacy_in, legacy_out = backend.parse_output(path)
    usage = backend.parse_usage(path, input_tokens=legacy_in, output_tokens=legacy_out)

    assert (legacy_in, legacy_out) == (160, 10)
    assert usage.legacy_input_tokens == legacy_in
    assert usage.legacy_output_tokens == legacy_out
