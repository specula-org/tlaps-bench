"""LiteLLM agent structured usage and native USD cost parsing."""

from __future__ import annotations

import json
from pathlib import Path

from evaluator.backends.litellm import LiteLLMBackend


def _request_usage(
    *,
    iteration: int = 1,
    input_tokens: int | None = None,
    output_tokens: int | None = None,
    cache_read: int | None = None,
    reasoning: int | None = None,
    model: str | None = "claude-sonnet-4-6",
    request_id: str | None = "chatcmpl-1",
    finish_reason: str | None = "stop",
    duration_secs: float | None = 1.5,
    cost: float | None = 0.002,
) -> dict[str, object]:
    event: dict[str, object] = {"type": "request_usage", "iteration": iteration}
    if input_tokens is not None:
        event["input_tokens"] = input_tokens
    if output_tokens is not None:
        event["output_tokens"] = output_tokens
    if cache_read is not None:
        event["cache_read_input_tokens"] = cache_read
    if reasoning is not None:
        event["reasoning_output_tokens"] = reasoning
    if model is not None:
        event["model"] = model
    if request_id is not None:
        event["request_id"] = request_id
    if finish_reason is not None:
        event["finish_reason"] = finish_reason
    if duration_secs is not None:
        event["duration_secs"] = duration_secs
    if cost is not None:
        event["costs"] = [{"amount": cost, "unit": "usd", "source": "litellm.response_cost"}]
    return event


def _aggregate(*, input_tokens: int, output_tokens: int, model_requests: int | None = None) -> dict[str, object]:
    event: dict[str, object] = {
        "type": "usage",
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
    }
    if model_requests is not None:
        event["model_requests"] = model_requests
    return event


def _write(path: Path, *events: dict[str, object]) -> str:
    path.write_text("".join(json.dumps(event) + "\n" for event in events))
    return str(path)


def _backend() -> LiteLLMBackend:
    return LiteLLMBackend(model="claude-sonnet-4-6")


def test_per_request_usage_and_native_cost_are_aggregated(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(iteration=1, input_tokens=100, output_tokens=10, cost=0.002),
        _request_usage(iteration=2, input_tokens=60, output_tokens=20, cost=0.001),
        _aggregate(input_tokens=160, output_tokens=30, model_requests=2),
    )

    usage = _backend().parse_usage(path, input_tokens=160, output_tokens=30)

    assert usage.input_tokens == 160
    assert usage.output_tokens == 30
    assert usage.model_requests == 2
    assert usage.status == "complete"
    assert [cost.to_dict() for cost in usage.costs] == [
        {"amount": 0.003, "unit": "usd", "source": "litellm.response_cost"}
    ]


def test_cache_and_reasoning_tokens_are_classifications(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(input_tokens=100, output_tokens=40, cache_read=30, reasoning=15),
        _aggregate(input_tokens=100, output_tokens=40, model_requests=1),
    )

    usage = _backend().parse_usage(path, input_tokens=100, output_tokens=40)

    assert usage.input_tokens == 100
    assert usage.output_tokens == 40
    assert usage.cache_read_input_tokens == 30
    assert usage.reasoning_output_tokens == 15
    # Classifications must not inflate the totals a second time.
    assert usage.input_tokens == 100
    assert usage.output_tokens == 40


def test_request_metadata_is_preserved(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(input_tokens=10, output_tokens=5, request_id="chatcmpl-abc", model="claude-3-7"),
        _aggregate(input_tokens=10, output_tokens=5, model_requests=1),
    )

    usage = _backend().parse_usage(path, input_tokens=10, output_tokens=5)

    request = usage.requests[0]
    assert request.request_id == "chatcmpl-abc"
    assert request.resolved_model == "claude-3-7"
    assert request.requested_model == "claude-sonnet-4-6"
    assert request.provider == "litellm"
    assert request.finish_reasons == ("stop",)
    assert request.duration_secs == 1.5


def test_partial_cost_coverage_is_a_lower_bound(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(iteration=1, input_tokens=100, output_tokens=10, cost=0.002),
        _request_usage(iteration=2, input_tokens=60, output_tokens=20, cost=None),
        _aggregate(input_tokens=160, output_tokens=30, model_requests=2),
    )

    usage = _backend().parse_usage(path, input_tokens=160, output_tokens=30)

    assert usage.status == "lower_bound"
    assert [cost.to_dict() for cost in usage.costs] == [
        {"amount": 0.002, "unit": "usd", "source": "litellm.response_cost"}
    ]
    assert any("lower bound" in warning for warning in usage.warnings)


def test_completion_error_marks_usage_as_partial(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(input_tokens=100, output_tokens=10),
        {"type": "error", "message": "provider rejected the request", "iteration": 2},
        _aggregate(input_tokens=100, output_tokens=10, model_requests=1),
    )

    usage = _backend().parse_usage(path, input_tokens=100, output_tokens=10)

    assert usage.status == "lower_bound"
    assert any("completion error" in warning for warning in usage.warnings)


def test_aggregate_disagreeing_with_events_is_flagged(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(input_tokens=100, output_tokens=10),
        _aggregate(input_tokens=100, output_tokens=10, model_requests=5),
    )

    usage = _backend().parse_usage(path, input_tokens=100, output_tokens=10)

    assert usage.status == "lower_bound"
    assert any("differs from per-request events" in warning for warning in usage.warnings)


def test_legacy_aggregate_only_output_is_a_lower_bound(tmp_path):
    """An older in-container agent emits no per-request events."""

    path = _write(
        tmp_path / "output.jsonl",
        _aggregate(input_tokens=120, output_tokens=45),
    )

    usage = _backend().parse_usage(path, input_tokens=120, output_tokens=45)

    assert usage.input_tokens == 120
    assert usage.output_tokens == 45
    assert usage.status == "lower_bound"
    assert any("per-request" in warning for warning in usage.warnings)


def test_no_model_request_is_an_exact_zero(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _aggregate(input_tokens=0, output_tokens=0, model_requests=0),
    )

    usage = _backend().parse_usage(path, input_tokens=0, output_tokens=0)

    assert usage.input_tokens == 0
    assert usage.output_tokens == 0
    assert usage.model_requests == 0
    assert usage.status == "complete"


def test_missing_output_is_unavailable_not_zero(tmp_path):
    usage = _backend().parse_usage(str(tmp_path / "missing.jsonl"), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert usage.to_dict()["input_tokens"] is None


def test_unreported_token_field_stays_null(tmp_path):
    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(output_tokens=10, input_tokens=None),
        _aggregate(input_tokens=0, output_tokens=10, model_requests=1),
    )

    usage = _backend().parse_usage(path, input_tokens=0, output_tokens=10)

    assert usage.input_tokens is None
    assert usage.output_tokens == 10


def test_truncated_run_without_aggregate_is_a_lower_bound(tmp_path):
    """A killed agent never writes its trailing total; what we have is a floor."""

    path = _write(
        tmp_path / "output.jsonl",
        _request_usage(input_tokens=100, output_tokens=10),
    )

    usage = _backend().parse_usage(path, input_tokens=100, output_tokens=10)

    assert usage.input_tokens == 100
    assert usage.status == "lower_bound"
    assert any("aggregate usage event missing" in warning for warning in usage.warnings)


def test_malformed_lines_are_ignored(tmp_path):
    path = tmp_path / "output.jsonl"
    path.write_text(
        "not json\n"
        + json.dumps(_request_usage(input_tokens=10, output_tokens=5))
        + "\n"
        + json.dumps(_aggregate(input_tokens=10, output_tokens=5, model_requests=1))
        + "\n"
    )

    usage = _backend().parse_usage(str(path), input_tokens=10, output_tokens=5)

    assert usage.input_tokens == 10
    assert usage.model_requests == 1
