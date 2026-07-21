"""Pi native JSONL structured-usage mapping and lifecycle behavior."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from evaluator.backends.pi import PiBackend

_MISSING = object()


def _write_jsonl(path: Path, *events: object) -> None:
    path.write_text("".join((event if isinstance(event, str) else json.dumps(event)) + "\n" for event in events))


def _native_usage(
    *,
    input_tokens: object = 100,
    output_tokens: object = 40,
    cache_read: object = 60,
    cache_write: object = 10,
    total_tokens: object = _MISSING,
    reasoning: object = 25,
    cost_total: object = 0.01,
    cache_write_1h: object = _MISSING,
) -> dict[str, object]:
    if total_tokens is _MISSING:
        assert all(isinstance(value, int) for value in (input_tokens, output_tokens, cache_read, cache_write))
        total_tokens = input_tokens + output_tokens + cache_read + cache_write  # type: ignore[operator]
    usage: dict[str, object] = {
        "input": input_tokens,
        "output": output_tokens,
        "cacheRead": cache_read,
        "cacheWrite": cache_write,
        "totalTokens": total_tokens,
        "cost": {
            "input": 0.001,
            "output": 0.006,
            "cacheRead": 0.0005,
            "cacheWrite": 0.0025,
            "total": cost_total,
        },
    }
    if reasoning is not _MISSING:
        usage["reasoning"] = reasoning
    if cache_write_1h is not _MISSING:
        usage["cacheWrite1h"] = cache_write_1h
    return usage


def _zero_usage() -> dict[str, object]:
    return _native_usage(
        input_tokens=0,
        output_tokens=0,
        cache_read=0,
        cache_write=0,
        total_tokens=0,
        reasoning=0,
        cost_total=0,
    )


def _assistant_message(
    *,
    usage: object = _MISSING,
    model: object = "requested-model",
    response_model: object = "resolved-model",
    provider: object = "openai",
    api: object = "openai-responses",
    response_id: object = "response-1",
    stop_reason: object = "stop",
    content: object = _MISSING,
    error_message: object = _MISSING,
) -> dict[str, object]:
    message: dict[str, object] = {
        "role": "assistant",
        "content": [] if content is _MISSING else content,
        "api": api,
        "provider": provider,
        "model": model,
        "usage": _native_usage() if usage is _MISSING else usage,
        "stopReason": stop_reason,
        "timestamp": 1_721_430_000_000,
    }
    if response_model is not _MISSING:
        message["responseModel"] = response_model
    if response_id is not _MISSING:
        message["responseId"] = response_id
    if error_message is not _MISSING:
        message["errorMessage"] = error_message
    return message


def _message_end(**overrides: object) -> dict[str, object]:
    return {"type": "message_end", "message": _assistant_message(**overrides)}


def test_multi_turn_tool_run_maps_each_finalized_assistant_request(tmp_path):
    output = tmp_path / "output.jsonl"
    first_usage = _native_usage(cache_write_1h=7)
    second_usage = _native_usage(
        input_tokens=50,
        output_tokens=20,
        cache_read=20,
        cache_write=5,
        reasoning=5,
        cost_total=0.004,
    )
    _write_jsonl(
        output,
        {"type": "session", "version": 3, "id": "session-1"},
        {"type": "agent_start"},
        {"type": "message_end", "message": {"role": "user", "usage": _native_usage()}},
        {
            "type": "message_update",
            "message": {"role": "assistant"},
            "assistantMessageEvent": {"type": "text_delta", "delta": "Proof "},
        },
        _message_end(usage=first_usage, stop_reason="toolUse"),
        {"type": "message_end", "message": {"role": "toolResult", "usage": _native_usage()}},
        {
            "type": "message_update",
            "message": {"role": "assistant"},
            "assistantMessageEvent": {"type": "text_delta", "delta": "done"},
        },
        _message_end(
            usage=second_usage,
            response_model=_MISSING,
            response_id=_MISSING,
            stop_reason="stop",
        ),
        {"type": "agent_end", "messages": []},
        {"type": "agent_settled"},
    )
    backend = PiBackend()

    transcript, input_tokens, output_tokens = backend.parse_output(str(output))
    usage = backend.parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == "Proof done"
    assert (input_tokens, output_tokens) == (245, 60)
    assert usage.status == "complete"
    assert usage.sources == ("pi_cli_message_end",)
    assert usage.model_requests == 2
    assert usage.input_tokens == 245
    assert usage.output_tokens == 60
    assert usage.cache_read_input_tokens == 80
    assert usage.cache_write_input_tokens == 15
    assert usage.reasoning_output_tokens == 30
    assert usage.model_time_secs is None
    assert usage.costs[0].amount == pytest.approx(0.014)
    assert usage.costs[0].unit == "usd"
    assert usage.costs[0].source == "pi.usage.cost.total"

    first, second = usage.requests
    assert first.input_tokens == 170
    assert first.output_tokens == 40
    assert first.cache_read_input_tokens == 60
    assert first.cache_write_input_tokens == 10
    assert first.reasoning_output_tokens == 25
    assert first.requested_model == "requested-model"
    assert first.resolved_model == "resolved-model"
    assert first.provider == "openai"
    assert first.endpoint == "openai-responses"
    assert first.provider_request_id == "response-1"
    assert first.finish_reasons == ("toolUse",)
    assert len(first.costs) == 1
    assert second.input_tokens == 75
    assert second.resolved_model == "requested-model"
    assert second.provider_request_id is None


def test_cache_write_1h_is_not_added_to_tokens_or_native_total_cost(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(cache_write_1h=9)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.input_tokens == 170
    assert usage.cache_write_input_tokens == 10
    assert usage.costs[0].amount == pytest.approx(0.01)


def test_message_start_and_end_do_not_duplicate_one_request(tmp_path):
    output = tmp_path / "output.jsonl"
    message = _assistant_message()
    _write_jsonl(
        output,
        {"type": "message_start", "message": message},
        {"type": "message_end", "message": message},
        {"type": "agent_settled"},
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.model_requests == 1


def test_valid_error_and_recovered_response_are_each_counted_once(tmp_path):
    output = tmp_path / "output.jsonl"
    failed_usage = _native_usage(input_tokens=20, output_tokens=2, cache_read=0, cache_write=0, reasoning=0)
    recovered_usage = _native_usage(input_tokens=30, output_tokens=5, cache_read=10, cache_write=0, reasoning=0)
    _write_jsonl(
        output,
        _message_end(usage=failed_usage, stop_reason="error", error_message="transient provider failure"),
        {"type": "agent_end", "messages": [], "willRetry": True},
        _message_end(usage=recovered_usage, stop_reason="stop"),
        {"type": "agent_end", "messages": [], "willRetry": False},
        {"type": "agent_settled"},
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.model_requests == 2
    assert (usage.input_tokens, usage.output_tokens) == (60, 7)
    assert [request.finish_reasons for request in usage.requests] == [("error",), ("stop",)]


def test_agent_end_without_agent_settled_retains_usage_as_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(), {"type": "agent_end", "messages": [], "willRetry": False})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert any("agent_settled was not observed" in warning for warning in usage.warnings)


def test_run_activity_after_agent_settled_cannot_be_reported_complete(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _message_end(),
        {"type": "agent_settled"},
        {"type": "agent_start"},
        _message_end(response_id="response-2"),
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 2
    assert any("activity after agent_settled" in warning for warning in usage.warnings)


def test_compaction_makes_visible_usage_a_lower_bound_without_fabricating_hidden_request(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _message_end(),
        {"type": "compaction_start", "reason": "threshold"},
        {"type": "compaction_end", "result": {"summary": "hidden model output"}},
        {"type": "agent_settled"},
    )
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert len(usage.requests) == 1
    assert any("summarizer model usage is not exposed" in warning for warning in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(output)) is True


def test_compaction_without_visible_assistant_usage_is_unavailable_but_retry_unsafe(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, {"type": "compaction_start", "reason": "threshold"}, {"type": "agent_settled"})
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.model_requests is None
    assert backend.retry_may_duplicate_model_work(str(output)) is True


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("input", _MISSING),
        ("input", None),
        ("input", True),
        ("output", "40"),
        ("cacheRead", 1.5),
        ("cacheWrite", -1),
        ("totalTokens", False),
    ],
)
def test_invalid_core_token_field_skips_request(field, value, tmp_path):
    output = tmp_path / "output.jsonl"
    native = _native_usage()
    if value is _MISSING:
        native.pop(field)
    else:
        native[field] = value
    _write_jsonl(output, _message_end(usage=native), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert usage.model_requests is None
    assert any("invalid core fields" in warning for warning in usage.warnings)


def test_total_token_mismatch_retains_components_only_as_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(total_tokens=999)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert (usage.input_tokens, usage.output_tokens, usage.model_requests) == (170, 40, 1)
    assert any("totalTokens mismatch" in warning for warning in usage.warnings)


@pytest.mark.parametrize("reasoning", [True, "25", 1.5, -1, 41])
def test_invalid_reasoning_is_discarded_without_losing_core_usage(reasoning, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(reasoning=reasoning)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert (usage.input_tokens, usage.output_tokens) == (170, 40)
    assert usage.reasoning_output_tokens is None
    assert any("reasoning" in warning for warning in usage.warnings)


def test_absent_optional_reasoning_can_still_be_complete(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(reasoning=_MISSING)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.reasoning_output_tokens is None


@pytest.mark.parametrize("cost_total", [None, True, "0.01", -1, float("inf"), float("nan")])
def test_invalid_cost_is_omitted_and_downgrades_known_tokens(cost_total, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(cost_total=cost_total)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.input_tokens == 170
    assert usage.model_requests == 1
    assert usage.costs == ()
    assert any("cost.total" in warning for warning in usage.warnings)


def test_missing_cost_object_is_omitted_and_downgrades_request(tmp_path):
    output = tmp_path / "output.jsonl"
    native = _native_usage()
    native.pop("cost")
    _write_jsonl(output, _message_end(usage=native), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.costs == ()


def test_zero_native_estimate_is_preserved_with_provenance_and_warning(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_native_usage(cost_total=0)), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.costs[0].amount == 0
    assert usage.costs[0].unit == "usd"
    assert usage.costs[0].source == "pi.usage.cost.total"
    assert any("zero USD estimate" in warning for warning in usage.warnings)


@pytest.mark.parametrize(("field", "value"), [("model", ""), ("provider", None), ("api", True)])
def test_invalid_required_metadata_retains_tokens_as_lower_bound(field, value, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(**{field: value}), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.input_tokens == 170
    assert usage.model_requests == 1
    assert any(field in warning for warning in usage.warnings)


def test_invalid_optional_metadata_and_stop_reason_are_omitted_and_flagged(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _message_end(response_model=3, response_id=False, stop_reason="unknown"),
        {"type": "agent_settled"},
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    request = usage.requests[0]
    assert request.resolved_model == "requested-model"
    assert request.provider_request_id is None
    assert request.finish_reasons == ()
    assert any("responseModel" in warning for warning in usage.warnings)
    assert any("responseId" in warning for warning in usage.warnings)
    assert any("stopReason" in warning for warning in usage.warnings)


def test_all_zero_placeholder_is_unavailable_instead_of_an_exact_free_request(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _message_end(usage=_zero_usage(), stop_reason="error"), {"type": "agent_settled"})

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert usage.model_requests is None
    assert any("all-zero" in warning for warning in usage.warnings)


def test_skipped_all_zero_retry_makes_later_known_usage_a_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _message_end(usage=_zero_usage(), stop_reason="error"),
        {"type": "agent_end", "willRetry": True},
        _message_end(),
        {"type": "agent_settled"},
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert any("all-zero" in warning for warning in usage.warnings)


def test_non_assistant_messages_and_unknown_events_do_not_affect_complete_usage(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {"type": "message_end", "message": {"role": "user", "usage": {"input": "bad"}}},
        {"type": "message_end", "message": {"role": "toolResult", "usage": _native_usage()}},
        {"type": "message_end", "message": {"role": "custom", "usage": _native_usage()}},
        {"type": "future_event", "usage": _native_usage()},
        _message_end(),
        {"type": "agent_settled"},
    )

    usage = PiBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "complete"
    assert usage.model_requests == 1


@pytest.mark.parametrize(
    "candidate",
    [
        {"type": "message_end"},
        {"type": "message_end", "message": {"role": "future-message-role"}},
    ],
)
def test_schema_invalid_message_candidate_is_lower_bound_and_retry_unsafe(candidate, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, candidate, _message_end(), {"type": "agent_settled"})
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert backend.retry_may_duplicate_model_work(str(output)) is True


@pytest.mark.parametrize(
    ("candidate", "warning"),
    [
        ({"type": []}, "missing or invalid type"),
        ({"type": "message_end", "message": {"role": []}}, "missing or invalid message role"),
        (
            _message_end(
                usage=_zero_usage(),
                response_id=_MISSING,
                stop_reason=[],
                content=[{"type": "text", "text": ""}],
                error_message="schema-invalid fallback",
            ),
            "all-zero usage placeholder",
        ),
    ],
)
def test_non_string_discriminators_are_rejected_without_aborting(candidate, warning, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, candidate, _message_end(), {"type": "agent_settled"})
    backend = PiBackend()

    transcript, input_tokens, output_tokens = backend.parse_output(str(output))
    usage = backend.parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == ""
    assert (input_tokens, output_tokens) == (170, 40)
    assert usage.status == "lower_bound"
    assert any(warning in item for item in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(output)) is True


def test_malformed_json_and_message_candidate_downgrade_known_usage(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        "not-json",
        {"type": "message_end"},
        _message_end(),
        {"type": "agent_settled"},
    )

    backend = PiBackend()
    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert any("malformed nonempty line" in warning for warning in usage.warnings)
    assert any("no message object" in warning for warning in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(output)) is True


@pytest.mark.parametrize("corrupt_line", ['{"type":"message_update"', "[]", '"not-an-event"'])
def test_malformed_nonempty_stream_is_retry_unsafe(corrupt_line, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, corrupt_line)
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert any("malformed nonempty line" in warning for warning in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(output)) is True


def test_non_utf8_existing_stream_is_retry_unsafe(tmp_path):
    output = tmp_path / "output.jsonl"
    output.write_bytes(b'{"type":"session","version":3}\n\xff\n')
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert any("UnicodeDecodeError" in warning for warning in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(output)) is True


def test_empty_existing_stream_remains_retry_safe(tmp_path):
    output = tmp_path / "output.jsonl"
    output.write_text("")
    backend = PiBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert backend.retry_may_duplicate_model_work(str(output)) is False


@pytest.mark.parametrize(
    ("event", "expected"),
    [
        (
            {
                "type": "message_start",
                "message": _assistant_message(usage=_zero_usage(), response_id=_MISSING),
            },
            True,
        ),
        (
            {
                "type": "message_update",
                "message": {"role": "assistant"},
                "assistantMessageEvent": {"type": "text_delta", "delta": "partial"},
            },
            True,
        ),
        (
            {
                "type": "message_end",
                "message": _assistant_message(
                    usage=_zero_usage(),
                    response_id=_MISSING,
                    stop_reason="stop",
                ),
            },
            True,
        ),
        ({"type": "agent_start"}, False),
        ({"type": "message_start", "message": {"role": "user"}}, False),
        ({"type": "tool_execution_start", "toolCallId": "tool-1", "toolName": "bash", "args": {}}, True),
        ({"type": "message_start"}, True),
        ({"type": "message_start", "message": {"role": "future-message-role"}}, True),
        (
            {
                "type": "message_start",
                "message": _assistant_message(
                    usage=_zero_usage(),
                    response_id=_MISSING,
                    stop_reason="error",
                    error_message="failed before provider stream",
                ),
            },
            True,
        ),
        (
            {
                "type": "message_start",
                "message": _assistant_message(
                    usage=_zero_usage(),
                    response_id=_MISSING,
                    stop_reason="error",
                    content=[{"type": "text", "text": ""}],
                    error_message="failed before provider stream",
                ),
            },
            False,
        ),
    ],
)
def test_native_lifecycle_activity_controls_safe_infra_retry(event, expected, tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, event)

    assert PiBackend().retry_may_duplicate_model_work(str(output)) is expected


def test_missing_output_is_unavailable_and_does_not_fabricate_activity(tmp_path):
    missing = tmp_path / "missing.jsonl"
    backend = PiBackend()

    transcript, input_tokens, output_tokens = backend.parse_output(str(missing))
    usage = backend.parse_usage(str(missing), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == ""
    assert (input_tokens, output_tokens) == (0, 0)
    assert usage.status == "unavailable"
    assert any("JSONL output unavailable" in warning for warning in usage.warnings)
    assert backend.retry_may_duplicate_model_work(str(missing)) is False


def test_pi_cli_and_kiro_provider_installs_are_pinned_to_researched_versions():
    script = Path("docker/install-scripts/install-pi.sh").read_text()
    docs = Path("docs/USAGE.md").read_text()

    assert "@earendil-works/pi-coding-agent@0.80.10" in script
    assert "pi install npm:pi-provider-kiro@0.8.1" in script
    assert "8dc78834cde4e329284cf505f9e3f99763df5529" in docs
    assert "d2f8dafb0f07409758797c880fbc3d526fa7c5c6" not in docs
