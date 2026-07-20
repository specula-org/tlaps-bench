"""Structured usage parsing for the native Codex CLI JSONL contract."""

import json
from pathlib import Path

import pytest

from evaluator.backends.codex import CodexBackend


def _write_jsonl(path: Path, *records: object) -> None:
    with path.open("w") as f:
        for record in records:
            if isinstance(record, str):
                f.write(record + "\n")
            else:
                f.write(json.dumps(record) + "\n")


def _completed_usage(**overrides: object) -> dict[str, object]:
    usage: dict[str, object] = {
        "input_tokens": 240,
        "cached_input_tokens": 180,
        "output_tokens": 60,
        "reasoning_output_tokens": 25,
    }
    usage.update(overrides)
    return {"type": "turn.completed", "usage": usage}


def test_complete_terminal_aggregate_maps_without_fabricating_request_or_cost(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {"type": "thread.started", "thread_id": "thread-1"},
        {
            "type": "item.completed",
            "item": {"type": "agent_message", "text": "Done"},
            # Future intermediate usage must not be added to the terminal total.
            "usage": {"input_tokens": 999, "output_tokens": 999},
        },
        _completed_usage(),
    )
    backend = CodexBackend(model="gpt-test")

    transcript, input_tokens, output_tokens = backend.parse_output(str(output))
    usage = backend.parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == "[AGENT] Done\n"
    assert (input_tokens, output_tokens) == (240, 60)
    assert usage.status == "complete"
    assert usage.input_tokens == 240
    assert usage.cache_read_input_tokens == 180
    assert usage.cache_write_input_tokens is None
    assert usage.output_tokens == 60
    assert usage.reasoning_output_tokens == 25
    assert usage.model_requests is None
    assert usage.model_time_secs is None
    assert usage.requests == ()
    assert usage.costs == ()
    assert usage.sources == ("codex_cli_turn_completed",)


def test_unknown_well_formed_events_do_not_downgrade_complete_usage(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, {"type": "future.event", "data": {"value": 1}}, _completed_usage())

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "complete"
    assert usage.warnings == ()


@pytest.mark.parametrize(
    ("event_type", "item_type"),
    [
        ("item.started", "reasoning"),
        ("item.updated", "command_execution"),
        ("item.completed", "agent_message"),
    ],
)
def test_native_item_lifecycle_proves_model_work_without_terminal_usage(tmp_path, event_type, item_type):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {"type": "thread.started", "thread_id": "thread-1"},
        {"type": "turn.started"},
        {"type": event_type, "item": {"id": "item-1", "type": item_type}},
        {"type": "turn.failed", "error": {"message": "connection lost"}},
    )

    assert CodexBackend().retry_may_duplicate_model_work(str(output)) is True


def test_lifecycle_or_malformed_item_shape_does_not_fabricate_model_work(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        "not-json",
        {"type": "thread.started", "thread_id": "thread-1"},
        {"type": "turn.started"},
        {"type": "item.started"},
        {"type": "item.completed", "item": {"id": "item-1", "type": ""}},
        {
            "type": "item.completed",
            "item": {"id": "item-warning", "type": "error", "message": "configuration warning"},
        },
        {"type": "error", "message": "request rejected"},
        {"type": "turn.failed", "error": {"message": "request rejected"}},
    )

    assert CodexBackend().retry_may_duplicate_model_work(str(output)) is False
    assert CodexBackend().retry_may_duplicate_model_work(str(tmp_path / "missing.jsonl")) is False


def test_multi_agent_activity_makes_parent_terminal_only_a_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {
            "type": "item.completed",
            "item": {
                "id": "item-1",
                "type": "collab_tool_call",
                "tool": "spawn_agent",
                "sender_thread_id": "parent",
                "receiver_thread_ids": ["child"],
                "status": "completed",
            },
        },
        _completed_usage(),
    )

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "lower_bound"
    assert (usage.input_tokens, usage.output_tokens) == (240, 60)
    assert any("covers only the parent thread" in warning for warning in usage.warnings)


def test_native_stream_lag_warning_downgrades_terminal_usage(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {
            "type": "item.completed",
            "item": {
                "id": "item-warning",
                "type": "error",
                "message": "in-process app-server event stream lagged; dropped 133 events",
            },
        },
        _completed_usage(),
    )

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "lower_bound"
    assert any("dropped JSONL events" in warning for warning in usage.warnings)


def test_native_stream_lag_makes_failed_launch_unsafe_to_retry(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {
            "type": "item.completed",
            "item": {
                "id": "item-warning",
                "type": "error",
                "message": "in-process app-server event stream lagged; dropped 3 events",
            },
        },
        {"type": "turn.failed", "error": {"message": "connection lost"}},
    )
    backend = CodexBackend()

    usage = backend.parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert backend.retry_may_duplicate_model_work(str(output)) is True
    assert usage.status == "unavailable"
    assert any("dropped JSONL events" in warning for warning in usage.warnings)


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("input_tokens", None),
        ("input_tokens", True),
        ("input_tokens", "240"),
        ("input_tokens", 2.5),
        ("input_tokens", -1),
        ("output_tokens", None),
        ("output_tokens", False),
        ("output_tokens", "60"),
        ("output_tokens", 1.5),
        ("output_tokens", -1),
    ],
)
def test_invalid_core_token_field_makes_usage_unavailable(tmp_path, field, value):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _completed_usage(**{field: value}))

    usage = CodexBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert usage.output_tokens is None
    assert any("invalid core fields" in warning for warning in usage.warnings)


def test_missing_optional_subsets_retain_core_totals_as_incomplete(tmp_path):
    output = tmp_path / "output.jsonl"
    terminal = _completed_usage()
    del terminal["usage"]["cached_input_tokens"]  # type: ignore[index]
    del terminal["usage"]["reasoning_output_tokens"]  # type: ignore[index]
    _write_jsonl(output, terminal)

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "incomplete"
    assert (usage.input_tokens, usage.output_tokens) == (240, 60)
    assert usage.cache_read_input_tokens is None
    assert usage.reasoning_output_tokens is None
    assert "missing cached_input_tokens" in usage.warnings[0]
    assert "missing reasoning_output_tokens" in usage.warnings[1]


def test_impossible_optional_subsets_are_dropped_and_flagged(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, _completed_usage(cached_input_tokens=241, reasoning_output_tokens=61))

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "incomplete"
    assert (usage.input_tokens, usage.output_tokens) == (240, 60)
    assert usage.cache_read_input_tokens is None
    assert usage.reasoning_output_tokens is None
    assert "cached input tokens exceed" in usage.warnings[0]
    assert "reasoning output tokens exceed" in usage.warnings[1]


def test_all_zero_terminal_is_not_treated_as_explicit_free_usage(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _completed_usage(input_tokens=0, cached_input_tokens=0, output_tokens=0, reasoning_output_tokens=0),
    )

    usage = CodexBackend().parse_usage(str(output), input_tokens=0, output_tokens=0)

    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert usage.output_tokens is None
    assert any("all-zero" in warning for warning in usage.warnings)


def test_failed_or_truncated_turn_without_terminal_usage_is_unavailable(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {"type": "item.completed", "item": {"type": "agent_message", "text": "Partial"}},
        {"type": "turn.failed", "error": {"message": "connection lost"}},
    )

    transcript, input_tokens, output_tokens = CodexBackend().parse_output(str(output))
    usage = CodexBackend().parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == "[AGENT] Partial\n"
    assert (input_tokens, output_tokens) == (0, 0)
    assert usage.status == "unavailable"
    assert usage.input_tokens is None
    assert any("failed before terminal usage" in warning for warning in usage.warnings)


def test_malformed_line_preserves_terminal_totals_only_as_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(output, "not-json", _completed_usage())

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "lower_bound"
    assert (usage.input_tokens, usage.output_tokens) == (240, 60)
    assert any("malformed nonempty line" in warning for warning in usage.warnings)


def test_multiple_terminal_aggregates_use_last_without_summing(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        _completed_usage(input_tokens=100, cached_input_tokens=50, output_tokens=20, reasoning_output_tokens=5),
        _completed_usage(input_tokens=240, cached_input_tokens=180, output_tokens=60, reasoning_output_tokens=25),
    )
    backend = CodexBackend()

    _transcript, input_tokens, output_tokens = backend.parse_output(str(output))
    usage = backend.parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert (input_tokens, output_tokens) == (240, 60)
    assert usage.status == "lower_bound"
    assert usage.input_tokens == 240
    assert any("multiple turn.completed" in warning for warning in usage.warnings)


def test_failed_and_completed_lifecycle_is_conservatively_a_lower_bound(tmp_path):
    output = tmp_path / "output.jsonl"
    _write_jsonl(
        output,
        {"type": "turn.failed", "error": {"message": "first failure"}},
        _completed_usage(),
    )

    usage = CodexBackend().parse_usage(str(output), input_tokens=240, output_tokens=60)

    assert usage.status == "lower_bound"
    assert (usage.input_tokens, usage.output_tokens) == (240, 60)
    assert any("both failed and completed" in warning for warning in usage.warnings)


def test_missing_jsonl_file_is_unavailable(tmp_path):
    missing = tmp_path / "missing.jsonl"
    backend = CodexBackend()

    transcript, input_tokens, output_tokens = backend.parse_output(str(missing))
    usage = backend.parse_usage(str(missing), input_tokens=input_tokens, output_tokens=output_tokens)

    assert transcript == ""
    assert (input_tokens, output_tokens) == (0, 0)
    assert usage.status == "unavailable"
    assert any("JSONL output unavailable" in warning for warning in usage.warnings)


def test_codex_cli_install_is_pinned_to_verified_jsonl_version():
    script = Path("docker/install-scripts/install-codex.sh").read_text()

    assert "@openai/codex@0.144.6" in script


def test_codex_command_disables_child_agent_features_for_exact_usage():
    command = CodexBackend(model="gpt-test").build_command("/workspace", "/result")

    overrides = {command[index + 1] for index, value in enumerate(command[:-1]) if value == "-c"}
    assert "features.multi_agent=false" in overrides
    assert "features.multi_agent_v2=false" in overrides
    assert "features.enable_fanout=false" in overrides


def test_codex_last_message_is_isolated_across_retries():
    assert CodexBackend().attempt_output_files() == ("codex_last_message.txt",)
