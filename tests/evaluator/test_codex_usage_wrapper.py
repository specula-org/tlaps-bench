"""Codex rollout-tree child usage extraction."""

import json
import sys
from pathlib import Path

import pytest

from evaluator.backends.codex_usage_wrapper import CODEX_CHILD_USAGE_VERSION, collect_child_usage, main


def _meta(
    session_id: str,
    thread_id: str,
    *,
    parent_thread_id: str | None = None,
    forked_from_id: str | None = None,
    model_provider: str | None = "openai",
) -> dict[str, object]:
    payload: dict[str, object] = {"session_id": session_id, "id": thread_id}
    if parent_thread_id is not None:
        payload["parent_thread_id"] = parent_thread_id
    if forked_from_id is not None:
        payload["forked_from_id"] = forked_from_id
    if model_provider is not None:
        payload["model_provider"] = model_provider
    return {"timestamp": "2026-07-28T00:00:00.000Z", "type": "session_meta", "payload": payload}


def _event(event_type: str, **payload: object) -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "event_msg",
        "payload": {"type": event_type, **payload},
    }


def _context(turn_id: str, model: str = "gpt-5.6-sol") -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "turn_context",
        "payload": {"turn_id": turn_id, "model": model},
    }


def _tool(name: str, call_id: str, arguments: dict[str, object] | None = None) -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "response_item",
        "payload": {
            "type": "function_call",
            "name": name,
            "call_id": call_id,
            "arguments": json.dumps(arguments or {}),
        },
    }


def _custom_tool(name: str, call_id: str, tool_input: str = "redacted by the audit") -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "response_item",
        "payload": {
            "type": "custom_tool_call",
            "name": name,
            "call_id": call_id,
            "input": tool_input,
        },
    }


def _tool_search(call_id: str) -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "response_item",
        "payload": {
            "type": "tool_search_call",
            "call_id": call_id,
            "status": "completed",
            "arguments": {"query": "redacted by the audit"},
        },
    }


def _response_tool(item_type: str, item_id: str, *, id_key: str = "id", **payload: object) -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "response_item",
        "payload": {"type": item_type, id_key: item_id, **payload},
    }


def _tokens(
    input_tokens: int,
    cached_input_tokens: int,
    output_tokens: int,
    reasoning_output_tokens: int,
    cache_write_input_tokens: int = 0,
) -> dict[str, object]:
    total_token_usage: dict[str, object] = {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "cache_write_input_tokens": cache_write_input_tokens,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning_output_tokens,
        "total_tokens": input_tokens + output_tokens,
    }
    return _event(
        "token_count",
        info={"total_token_usage": total_token_usage},
    )


def _write_rollout(path: Path, *records: object) -> None:
    with path.open("w") as rollout:
        for record in records:
            if isinstance(record, str):
                rollout.write(record + "\n")
            else:
                rollout.write(json.dumps(record) + "\n")


def _rollout(
    tmp_path: Path,
    thread_id: str,
    *records: object,
    parent_thread_id: str | None = None,
    forked_from_id: str | None = None,
    model_provider: str | None = "openai",
) -> Path:
    path = tmp_path / f"rollout-{thread_id}.jsonl"
    _write_rollout(
        path,
        _meta(
            "root",
            thread_id,
            parent_thread_id=parent_thread_id,
            forked_from_id=forked_from_id,
            model_provider=model_provider,
        ),
        *records,
    )
    return path


def _turn(
    turn_id: str,
    usage: tuple[int, int, int, int] | tuple[int, int, int, int, int] | None = None,
    end: str | None = "task_complete",
    model: str = "gpt-5.6-sol",
) -> tuple[dict[str, object], ...]:
    records = [_event("task_started", turn_id=turn_id), _context(turn_id, model)]
    if usage is not None:
        records.append(_tokens(*usage))
    if end is not None:
        records.append(_event(end, turn_id=turn_id))
    return tuple(records)


def _usage(audit: dict[str, object]) -> tuple[object, ...]:
    return tuple(
        audit[field]
        for field in (
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
            "reasoning_output_tokens",
        )
    )


def _request_usage(request: object) -> tuple[object, ...]:
    assert isinstance(request, dict)
    return tuple(
        request[field]
        for field in (
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
            "reasoning_output_tokens",
            "model",
            "provider",
        )
    )


def test_nested_forks_subtract_each_immediate_parent_baseline(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (240, 180, 60, 25, 20)))
    child_path = _rollout(
        tmp_path,
        "child",
        # Forked history retains the parent's metadata, lifecycle, and cumulative usage.
        _meta("root", "root"),
        *_turn("root-turn", (240, 180, 60, 25, 20)),
        *_turn("child-turn", (300, 220, 80, 30, 30)),
        parent_thread_id="root",
        forked_from_id="root",
    )
    grandchild_path = _rollout(
        tmp_path,
        "grandchild",
        _meta("root", "child", parent_thread_id="root", forked_from_id="root"),
        *_turn("root-turn", (240, 180, 60, 25, 20)),
        *_turn("child-turn", (300, 220, 80, 30, 30)),
        *_turn("grandchild-turn", (330, 240, 90, 33, 33)),
        parent_thread_id="child",
        forked_from_id="child",
    )

    audit = collect_child_usage("root", (root_path, child_path, grandchild_path))

    assert audit["complete"] is True
    assert audit["warning_codes"] == []
    assert audit["child_count"] == 2
    assert _usage(audit) == (90, 60, 13, 30, 8)
    assert [_request_usage(request) for request in audit["requests"]] == [
        (240, 180, 20, 60, 25, "gpt-5.6-sol", "openai"),
        (60, 40, 10, 20, 5, "gpt-5.6-sol", "openai"),
        (30, 20, 3, 10, 3, "gpt-5.6-sol", "openai"),
    ]


def test_duplicate_snapshots_are_ignored_but_identical_request_deltas_are_kept(tmp_path):
    turn_id = "root-turn"
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id=turn_id),
        _context(turn_id),
        _tokens(200_000, 0, 0, 0),
        _tokens(200_000, 0, 0, 0),
        _tokens(400_000, 0, 0, 0),
        _event("task_complete", turn_id=turn_id),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is True
    assert audit["warning_codes"] == []
    assert [_request_usage(request) for request in audit["requests"]] == [
        (200_000, 0, 0, 0, 0, "gpt-5.6-sol", "openai"),
        (200_000, 0, 0, 0, 0, "gpt-5.6-sol", "openai"),
    ]


def test_default_service_tier_keeps_usage_complete(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("thread_settings_applied", thread_settings={"service_tier": None}),
        *_turn("root-turn", (10, 0, 1, 0)),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is True
    assert audit["warning_codes"] == []


def test_nonstandard_service_tier_makes_cost_audit_incomplete(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("thread_settings_applied", thread_settings={"service_tier": "priority"}),
        *_turn("root-turn", (10, 0, 1, 0)),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "unsupported_service_tier" in audit["warning_codes"]


def test_request_model_is_required(tmp_path):
    turn_id = "root-turn"
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id=turn_id),
        _tokens(10, 0, 1, 0),
        _event("task_complete", turn_id=turn_id),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "request_model_missing" in audit["warning_codes"]
    assert _request_usage(audit["requests"][0])[-2:] == (None, "openai")


def test_conflicting_turn_models_are_not_selected_arbitrarily(tmp_path):
    turn_id = "root-turn"
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id=turn_id),
        _context(turn_id, "gpt-5.6-sol"),
        _context(turn_id, "gpt-5.5"),
        _tokens(10, 0, 1, 0),
        _event("task_complete", turn_id=turn_id),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "request_model_conflict" in audit["warning_codes"]
    assert _request_usage(audit["requests"][0])[-2:] == (None, "openai")


def test_request_provider_is_required(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        *_turn("root-turn", (10, 0, 1, 0)),
        model_provider=None,
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "request_provider_missing" in audit["warning_codes"]
    assert _request_usage(audit["requests"][0])[-2:] == ("gpt-5.6-sol", None)


def test_aborted_child_keeps_observed_native_delta_as_a_lower_bound(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        *_turn("child-turn", (15, 5, 7, 2), end="turn_aborted"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_lifecycle_invalid" in audit["warning_codes"]
    assert audit["child_count"] == 1
    assert _usage(audit) == (15, 5, 0, 7, 2)


def test_cache_read_and_write_cannot_exceed_total_input(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        *_turn("child-turn", (10, 8, 4, 1, 3)),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "rollout_invalid" in audit["warning_codes"]
    assert _usage(audit) == (0, 0, 0, 0, 0)


def test_damaged_fork_prefix_never_overcounts_inherited_parent_usage(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (100, 50, 20, 4)))
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="root-turn"),
        "{not-json",
        _tokens(100, 50, 20, 4),
        _event("task_complete", turn_id="root-turn"),
        *_turn("child-turn", (140, 70, 30, 6)),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "fork_baseline_unavailable" in audit["warning_codes"]
    assert (audit["input_tokens"], audit["output_tokens"]) == (0, 0)


def test_regressing_fork_prefix_never_creates_an_undersized_baseline(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (100, 50, 20, 4)))
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="root-turn"),
        _tokens(100, 50, 20, 4),
        _tokens(90, 45, 18, 3),
        _event("task_complete", turn_id="root-turn"),
        *_turn("child-turn", (140, 70, 30, 6)),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "fork_baseline_unavailable" in audit["warning_codes"]
    assert _usage(audit) == (0, 0, 0, 0, 0)


def test_child_without_a_valid_path_to_root_is_not_counted(tmp_path):
    root_path = _rollout(tmp_path, "root")
    grandchild_path = _rollout(
        tmp_path,
        "grandchild",
        *_turn("grandchild-turn", (40, 20, 10, 2)),
        parent_thread_id="grandchild",
        forked_from_id="grandchild",
    )

    audit = collect_child_usage("root", (root_path, grandchild_path))

    assert audit["complete"] is False
    assert "thread_tree_invalid" in audit["warning_codes"]
    assert audit["input_tokens"] == 0


def test_completed_child_turn_without_native_usage_is_not_exact(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(tmp_path, "child", *_turn("child-turn"), parent_thread_id="root")

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_usage_missing" in audit["warning_codes"]
    assert audit["child_count"] == 1


def test_unchanged_native_usage_snapshot_does_not_prove_child_usage(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        *_turn("child-turn", (0, 0, 0, 0)),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_usage_missing" in audit["warning_codes"]
    assert _usage(audit) == (0, 0, 0, 0, 0)


def test_counter_regression_keeps_the_last_safe_usage_prefix(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (100, 50, 20, 4)))
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="root-turn"),
        _tokens(100, 50, 20, 4),
        _event("task_complete", turn_id="root-turn"),
        _event("task_started", turn_id="child-turn"),
        _context("child-turn"),
        _tokens(140, 70, 30, 6),
        _tokens(130, 65, 28, 5),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_usage_counter_invalid" in audit["warning_codes"]
    assert _usage(audit) == (40, 20, 0, 10, 2)


def test_usage_change_outside_an_active_turn_is_not_reported_as_exact(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        *_turn("child-turn", (10, 5, 4, 1)),
        _tokens(20, 10, 8, 2),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_lifecycle_invalid" in audit["warning_codes"]
    assert _usage(audit) == (20, 10, 0, 8, 2)


def test_overlapping_child_turns_are_not_reported_as_exact(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="first-turn"),
        _event("task_started", turn_id="second-turn"),
        _tokens(20, 10, 8, 2),
        _event("task_complete", turn_id="second-turn"),
        _event("task_complete", turn_id="first-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_lifecycle_invalid" in audit["warning_codes"]
    assert _usage(audit) == (20, 10, 0, 8, 2)


def test_duplicate_thread_rollouts_are_not_arbitrarily_counted(tmp_path):
    root_path = _rollout(tmp_path, "root")
    first_child_path = tmp_path / "rollout-child-first.jsonl"
    second_child_path = tmp_path / "rollout-child-second.jsonl"
    _write_rollout(
        first_child_path,
        _meta("root", "child", parent_thread_id="root"),
        *_turn("child-turn", (10, 5, 4, 1)),
    )
    _write_rollout(
        second_child_path,
        _meta("root", "child", parent_thread_id="root"),
        *_turn("child-turn", (100, 50, 40, 10)),
    )

    audit = collect_child_usage("root", (root_path, first_child_path, second_child_path))

    assert audit["complete"] is False
    assert "duplicate_thread_rollout" in audit["warning_codes"]
    assert audit["child_count"] == 0
    assert _usage(audit) == (0, 0, 0, 0, 0)


def test_persisted_child_reference_requires_a_matching_rollout(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("sub_agent_activity", agent_thread_id="missing-child", kind="started"),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "referenced_child_rollout_missing" in audit["warning_codes"]


def test_session_tree_tool_audit_counts_child_dispatches_and_continuations(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _context("child-turn"),
        _tool("exec_command", "child-call", {"cmd": "/bin/bash -lc 'tlapm Child.tla'"}),
        _tool("write_stdin", "child-poll", {"session_id": 1}),
        _tool("wait", "child-code-mode-poll", {"cell_id": "cell-1"}),
        _custom_tool("wait", "defensive-custom-poll", '{"cell_id":"cell-1"}'),
        _custom_tool("apply_patch", "child-edit"),
        _tool_search("child-search"),
        _tokens(130, 60, 30, 6),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["tool_calls_scope"] == "session_tree"
    assert audit["tool_calls"] == {
        "total": 6,
        "tlaps": 1,
        "tlc": 0,
        "apalache": 0,
        "other": 5,
        "available": True,
        "complete": True,
        "is_lower_bound": False,
        "warnings": [],
    }
    assert "/bin/bash" not in json.dumps(audit)


@pytest.mark.parametrize(
    "dispatch",
    (
        _tool("wait", "function-wait", {"cell_id": "cell-1"}),
        _tool("write_stdin", "function-write", {"session_id": 1}),
        _custom_tool("wait", "custom-wait", '{"cell_id":"cell-1"}'),
        _custom_tool("write_stdin", "custom-write", '{"session_id":1}'),
    ),
    ids=("function-wait", "function-write-stdin", "custom-wait", "custom-write-stdin"),
)
def test_session_tree_tool_audit_counts_each_continuation_dispatch(dispatch, tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id="root-turn"),
        dispatch,
        _event("task_complete", turn_id="root-turn"),
    )

    audit = collect_child_usage("root", (root_path,))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["other"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True


@pytest.mark.parametrize(
    "dispatch",
    (
        _response_tool("image_generation_call", "image-call"),
        _response_tool(
            "local_shell_call",
            "shell-call",
            id_key="call_id",
            action={"command": "tlapm Local.tla"},
        ),
    ),
    ids=("image-generation", "local-shell-call-id"),
)
def test_session_tree_tool_audit_counts_response_tool_variants(dispatch, tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id="root-turn"),
        dispatch,
        _event("task_complete", turn_id="root-turn"),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["tool_calls"]["total"] == 1
    assert audit["tool_calls"]["complete"] is True
    if dispatch["payload"]["type"] == "image_generation_call":
        assert audit["tool_calls"]["other"] == 1
    else:
        assert audit["tool_calls"]["tlaps"] == 1


def test_session_tree_tool_audit_counts_root_and_child_without_replaying_fork_prefix(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id="root-turn"),
        _tool("exec_command", "root-call", {"cmd": "tlapm Root.tla"}),
        _event("task_complete", turn_id="root-turn"),
    )
    child_path = _rollout(
        tmp_path,
        "child",
        _meta("root", "root"),
        _event("task_started", turn_id="root-turn"),
        _tool("exec_command", "root-call", {"cmd": "tlapm Root.tla"}),
        _event("task_complete", turn_id="root-turn"),
        _event("task_started", turn_id="child-turn"),
        _custom_tool("apply_patch", "child-edit"),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"], audit["tool_calls"]["other"]) == (
        2,
        1,
        1,
    )
    assert audit["tool_calls"]["complete"] is True


def test_code_mode_child_exec_uses_literal_nested_command_for_classification(tmp_path):
    secret_command = "tlapm PrivateChild.tla"
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _custom_tool(
            "exec",
            "code-mode",
            '// @exec: {"max_output_tokens": 100000}\n'
            "const results = await Promise.all([\n"
            '  tools.exec_command({cmd: "echo ready"}),\n'
            f'  tools.exec_command({{cmd: "{secret_command}"}}),\n'
            "]);\ntext(results.length);",
        ),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True
    assert secret_command not in json.dumps(audit)


def test_non_code_mode_shell_command_uses_its_native_command_field(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _tool("shell_command", "shell", {"command": ["tlapm", "Child.tla"]}),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True


@pytest.mark.parametrize(
    "source",
    (
        '// tools.exec_command({cmd: "tlapm Comment.tla"});\ntext("done");',
        "const example = 'tools.exec_command({cmd: \"tlapm String.tla\"})'; text(example);",
        'const cmd = "tlapm Dynamic.tla"; await tools.exec_command({cmd});',
        "await tools.exec_command({cmd: `tlapm ${name}.tla`});",
        'await tools.exec_command({cmd: "tlapm First.tla", cmd: "echo safe"});',
        'const opts = {cmd: "echo safe"}; await tools.exec_command({cmd: "tlapm Spread.tla", ...opts});',
        'await tools.exec_command({cmd: "tlapm Computed.tla", ["cmd"]: "echo safe"});',
        'await tools.exec_command({cmd: "tlapm Broken.tla"',
    ),
    ids=("comment", "string", "dynamic", "template", "duplicate", "spread", "computed", "malformed"),
)
def test_code_mode_child_exec_is_conservative_for_nonliteral_nested_commands(source, tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _custom_tool("exec", "code-mode", source),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["other"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True


def test_aborted_child_can_still_enumerate_observed_tool_calls_exactly(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _tool("exec_command", "child-call", {"cmd": "tlapm Child.tla"}),
        _event("turn_aborted", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["tool_calls"]["total"] == 1
    assert audit["tool_calls"]["tlaps"] == 1
    assert audit["tool_calls"]["complete"] is True
    assert audit["tool_calls"]["is_lower_bound"] is False


def test_replayed_anonymous_child_dispatch_is_one_lower_bound_witness(tmp_path):
    root_path = _rollout(tmp_path, "root")
    anonymous = _tool("exec_command", None, {"cmd": "tlapm Child.tla"})
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        anonymous,
        anonymous,
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["is_lower_bound"] is True


def test_stable_child_id_dominates_anonymous_dispatch_witness(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _tool("exec_command", "stable", {"cmd": "tlapm Child.tla"}),
        _tool("exec_command", None, {"cmd": "tlapm Child.tla"}),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is False
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_id_invalid" in warning for warning in audit["tool_calls"]["warnings"])


def test_duplicate_native_child_dispatch_is_deduplicated_and_downgraded(tmp_path):
    root_path = _rollout(tmp_path, "root")
    dispatch = _tool("exec_command", "duplicate", {"cmd": "tlapm Child.tla"})
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        dispatch,
        dispatch,
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_id_duplicate" in warning for warning in audit["tool_calls"]["warnings"])


def test_direct_child_preserves_tool_evidence_before_its_first_turn(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _tool("exec_command", "early", {"cmd": "tlapm Child.tla"}),
        _event("task_started", turn_id="child-turn"),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_lifecycle_invalid" in warning for warning in audit["tool_calls"]["warnings"])


def test_forked_child_preserves_unmatched_prefix_tool_as_a_lower_bound(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn"))
    child_path = _rollout(
        tmp_path,
        "child",
        _tool("exec_command", "early-child", {"cmd": "tlapm Child.tla"}),
        _event("task_started", turn_id="child-turn"),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_boundary_unavailable" in warning for warning in audit["tool_calls"]["warnings"])


def test_session_tree_keeps_root_but_not_ambiguous_fork_prefix_tool(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id="root-turn"),
        _tool("exec_command", "parent-call", {"cmd": "tlapm Parent.tla"}),
        _event("task_complete", turn_id="root-turn"),
    )
    child_path = _rollout(
        tmp_path,
        "child",
        _tool("exec_command", "parent-call", {"cmd": "tlapm Conflicting.tla"}),
        _event("task_started", turn_id="child-turn"),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_boundary_unavailable" in warning for warning in audit["tool_calls"]["warnings"])


def test_forked_child_idless_prefix_tool_is_ambiguous_not_an_exact_zero(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn"))
    child_path = _rollout(
        tmp_path,
        "child",
        _tool("exec_command", None, {"cmd": "tlapm Ambiguous.tla"}),
        _event("task_started", turn_id="child-turn"),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["tool_calls"]["total"] == 0
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_boundary_unavailable" in warning for warning in audit["tool_calls"]["warnings"])


def test_invalid_usage_telemetry_does_not_downgrade_child_tool_enumeration(tmp_path):
    root_path = _rollout(tmp_path, "root")
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="child-turn"),
        _context("child-turn"),
        _tool("exec_command", "child-call", {"cmd": "tlapm Child.tla"}),
        _event("token_count", info={"total_token_usage": {"input_tokens": 1}}),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True


def test_invalid_parent_usage_telemetry_does_not_hide_forked_child_tools(tmp_path):
    invalid_tokens = _event("token_count", info={"total_token_usage": {"input_tokens": 1}})
    root_path = _rollout(
        tmp_path,
        "root",
        _event("task_started", turn_id="root-turn"),
        _context("root-turn"),
        invalid_tokens,
        _event("task_complete", turn_id="root-turn"),
    )
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="root-turn"),
        _event("task_complete", turn_id="root-turn"),
        _event("task_started", turn_id="child-turn"),
        _context("child-turn"),
        _tool("exec_command", "child-call", {"cmd": "tlapm Child.tla"}),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert (audit["tool_calls"]["total"], audit["tool_calls"]["tlaps"]) == (1, 1)
    assert audit["tool_calls"]["complete"] is True


def test_forked_child_without_an_own_turn_does_not_claim_exact_zero_tools(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (10, 5, 2, 1)))
    child_path = _rollout(
        tmp_path,
        "child",
        _meta("root", "root"),
        *_turn("root-turn", (10, 5, 2, 1)),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["tool_calls"]["total"] == 0
    assert audit["tool_calls"]["complete"] is False
    assert audit["tool_calls"]["is_lower_bound"] is True
    assert any("child_tool_lifecycle_invalid" in warning for warning in audit["tool_calls"]["warnings"])


def test_wrapper_streams_codex_then_appends_one_finished_audit(tmp_path, monkeypatch, capsys):
    codex_home = tmp_path / "codex-home"
    fake_codex = tmp_path / "fake_codex.py"
    fake_codex.write_text(
        """
import datetime
import json
import os
from pathlib import Path

root = "root-thread"
print(json.dumps({"type": "thread.started", "thread_id": root}), flush=True)
today = datetime.datetime.now().astimezone().date()
day_dir = Path(os.environ["CODEX_HOME"]) / "sessions" / str(today.year) / f"{today.month:02d}" / f"{today.day:02d}"
day_dir.mkdir(parents=True)
meta = {
    "timestamp": "now",
    "type": "session_meta",
    "payload": {"session_id": root, "id": root, "model_provider": "openai"},
}
(day_dir / f"rollout-now-{root}.jsonl").write_text(json.dumps(meta) + "\\n")
print(json.dumps({"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}}), flush=True)
""".lstrip()
    )
    monkeypatch.setenv("CODEX_HOME", str(codex_home))

    return_code = main(["--", sys.executable, str(fake_codex)])
    records = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert return_code == 0
    assert [record["type"] for record in records] == [
        "tlaps.codex_child_usage.started",
        "thread.started",
        "turn.completed",
        "tlaps.codex_child_usage",
    ]
    assert records[-1] == {
        "type": "tlaps.codex_child_usage",
        "version": CODEX_CHILD_USAGE_VERSION,
        "tool_calls_scope": "session_tree",
        "root_thread_id": "root-thread",
        "child_count": 0,
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "requests": [],
        "complete": True,
        "warning_codes": [],
        "tool_calls": {
            "total": 0,
            "tlaps": 0,
            "tlc": 0,
            "apalache": 0,
            "other": 0,
            "available": True,
            "complete": True,
            "is_lower_bound": False,
            "warnings": [],
        },
    }
