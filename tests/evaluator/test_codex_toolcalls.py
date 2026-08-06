"""Codex tool-call lifecycle and child-audit integration."""

import json
from itertools import permutations

from evaluator.backends.codex import CodexBackend
from evaluator.backends.codex_usage_wrapper import CODEX_CHILD_USAGE_VERSION


def _write_jsonl(path, *events):
    with path.open("w") as output:
        for event in events:
            output.write((event if isinstance(event, str) else json.dumps(event)) + "\n")
    return str(path)


def _item(event_type, item_id, item_type, command=None):
    item = {"id": item_id, "type": item_type}
    if command is not None:
        item["command"] = command
    return {"type": event_type, "item": item}


def _summary(backend, path):
    return backend.parse_run_metadata(path)["tool_calls"]


def test_complete_root_counts_started_items_once_by_id(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        _item("item.completed", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        _item("item.started", "edit", "file_change"),
        _item("item.completed", "edit", "file_change"),
        _item("item.started", "todo", "todo_list"),
        _item("item.completed", "todo", "todo_list"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    assert _summary(CodexBackend(), path) == {
        "total": 3,
        "tlaps": 1,
        "tlc": 0,
        "apalache": 0,
        "other": 2,
        "available": True,
        "complete": True,
        "is_lower_bound": False,
        "warnings": [],
    }


def test_each_todo_update_is_a_distinct_update_plan_dispatch(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "todo", "todo_list"),
        _item("item.updated", "todo", "todo_list"),
        _item("item.updated", "todo", "todo_list"),
        _item("item.completed", "todo", "todo_list"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["other"]) == (3, 3)
    assert summary["complete"] is True
    assert summary["warnings"] == []


def test_todo_update_outside_its_lifecycle_is_a_lower_bound(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "todo", "todo_list"),
        _item("item.completed", "todo", "todo_list"),
        _item("item.updated", "todo", "todo_list"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["other"]) == (2, 2)
    assert summary["is_lower_bound"] is True
    assert any("invalid update lifecycle" in warning for warning in summary["warnings"])


def test_orphan_todo_update_is_observed_but_not_claimed_exact(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.updated", "todo", "todo_list"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["other"]) == (1, 1)
    assert summary["is_lower_bound"] is True


def test_unfinished_todo_updates_are_counted_as_a_lower_bound(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "todo", "todo_list"),
        _item("item.updated", "todo", "todo_list"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["other"]) == (2, 2)
    assert summary["is_lower_bound"] is True
    assert any("did not complete" in warning for warning in summary["warnings"])


def test_duplicate_native_item_lifecycle_is_deduplicated_but_not_claimed_exact(tmp_path):
    start = _item("item.started", "command", "command_execution", "tlapm Foo.tla")
    completed = _item("item.completed", "command", "command_execution", "tlapm Foo.tla")
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        start,
        start,
        completed,
        completed,
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["is_lower_bound"] is True


def test_started_only_call_is_counted_as_a_lower_bound(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["complete"] is False
    assert summary["is_lower_bound"] is True
    assert any("did not complete" in warning for warning in summary["warnings"])


def test_completed_only_call_is_counted_as_a_lower_bound(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.completed", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["complete"] is False
    assert summary["is_lower_bound"] is True
    assert any("without a recorded start" in warning for warning in summary["warnings"])


def test_completed_only_file_change_remains_a_lower_bound(tmp_path):
    # Codex currently emits matching started/completed file-change events. A
    # completed-only record therefore means the dispatch boundary was lost.
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.completed", "edit", "file_change"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["other"]) == (1, 1)
    assert summary["is_lower_bound"] is True
    assert any("without a recorded start" in warning for warning in summary["warnings"])


def test_anonymous_started_completed_pair_is_counted_once(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", None, "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        _item("item.completed", None, "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["is_lower_bound"] is True
    assert any("without IDs" in warning for warning in summary["warnings"])


def test_replayed_anonymous_lifecycle_records_do_not_break_lower_bound(tmp_path):
    start = _item("item.started", None, "command_execution", "/bin/bash -lc 'tlapm Foo.tla'")
    completed = _item("item.completed", None, "command_execution", "/bin/bash -lc 'tlapm Foo.tla'")
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        start,
        start,
        completed,
        completed,
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["is_lower_bound"] is True


def test_dropped_event_marker_downgrades_an_otherwise_clean_stream(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {
            "type": "item.completed",
            "item": {
                "id": "warning",
                "type": "error",
                "message": "in-process app-server event stream lagged; dropped 3 events",
            },
        },
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["is_lower_bound"] is True
    assert any("dropped JSONL events" in warning for warning in summary["warnings"])


def test_item_activity_after_turn_completed_downgrades_the_stream(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        _item("item.started", "late", "command_execution", "tlapm Late.tla"),
        _item("item.completed", "late", "command_execution", "tlapm Late.tla"),
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["is_lower_bound"] is True
    assert any("after its terminal" in warning for warning in summary["warnings"])


def test_turn_activity_after_turn_completed_downgrades_the_stream(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {"type": "turn.started"},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["is_lower_bound"] is True


def test_thread_started_after_terminal_is_not_a_clean_lifecycle(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {"type": "thread.started", "thread_id": "root"},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["is_lower_bound"] is True
    assert any("invalid thread/turn event order" in warning for warning in summary["warnings"])


def test_only_canonical_root_lifecycle_order_is_complete(tmp_path):
    canonical = (
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "tlapm Foo.tla"),
        _item("item.completed", "command", "command_execution", "tlapm Foo.tla"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    for index, events in enumerate(permutations(canonical)):
        path = _write_jsonl(tmp_path / f"order-{index}.jsonl", *events)
        summary = _summary(CodexBackend(), path)

        assert summary["complete"] is (events == canonical)


def test_complete_session_tree_audit_replaces_cli_root_events(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "spawn", "collab_tool_call"),
        _item("item.completed", "spawn", "collab_tool_call"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {
            "type": "tlaps.codex_child_usage",
            "version": CODEX_CHILD_USAGE_VERSION,
            "tool_calls_scope": "session_tree",
            "root_thread_id": "root",
            "tool_calls": {
                "total": 2,
                "tlaps": 1,
                "tlc": 1,
                "apalache": 0,
                "other": 0,
                "available": True,
                "complete": True,
                "is_lower_bound": False,
                "warnings": [],
            },
        },
    )

    assert _summary(CodexBackend(), path) == {
        "total": 2,
        "tlaps": 1,
        "tlc": 1,
        "apalache": 0,
        "other": 0,
        "available": True,
        "complete": True,
        "is_lower_bound": False,
        "warnings": [],
    }


def test_lower_bound_session_tree_audit_is_not_added_to_cli_root_events(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "tlapm Root.tla"),
        _item("item.completed", "command", "command_execution", "tlapm Root.tla"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {
            "type": "tlaps.codex_child_usage",
            "version": CODEX_CHILD_USAGE_VERSION,
            "tool_calls_scope": "session_tree",
            "root_thread_id": "root",
            "tool_calls": {
                "total": 1,
                "tlaps": 0,
                "tlc": 0,
                "apalache": 0,
                "other": 1,
                "available": True,
                "complete": False,
                "is_lower_bound": True,
                "warnings": ["rollout audit incomplete"],
            },
        },
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"], summary["other"]) == (1, 0, 1)
    assert summary["is_lower_bound"] is True
    assert summary["warnings"] == ["rollout audit incomplete"]


def test_started_child_audit_that_never_finishes_is_a_lower_bound(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["is_lower_bound"] is True
    assert any("missing or ambiguous" in warning for warning in summary["warnings"])


def test_legacy_child_audit_does_not_fall_back_to_nested_cli_commands(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "tlaps.codex_child_usage.started", "version": 4},
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "tlaps", "command_execution", "tlapm Foo.tla"),
        _item("item.completed", "tlaps", "command_execution", "tlapm Foo.tla"),
        _item("item.started", "tlc", "command_execution", "tlc Foo.tla"),
        _item("item.completed", "tlc", "command_execution", "tlc Foo.tla"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {
            "type": "tlaps.codex_child_usage",
            "version": 4,
            "root_thread_id": "root",
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
        },
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"], summary["tlc"]) == (0, 0, 0)
    assert summary["is_lower_bound"] is True
    assert any("unsupported version" in warning for warning in summary["warnings"])


def test_session_tree_audit_before_cli_activity_is_not_trusted(tmp_path):
    audit = {
        "type": "tlaps.codex_child_usage",
        "version": CODEX_CHILD_USAGE_VERSION,
        "tool_calls_scope": "session_tree",
        "root_thread_id": "root",
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
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
        audit,
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "tlapm Foo.tla"),
        _item("item.completed", "command", "command_execution", "tlapm Foo.tla"),
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["is_lower_bound"] is True
    assert any("invalid stream position" in warning for warning in summary["warnings"])


def test_session_tree_sentinel_after_audit_is_not_trusted(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {
            "type": "tlaps.codex_child_usage",
            "version": CODEX_CHILD_USAGE_VERSION,
            "tool_calls_scope": "session_tree",
            "root_thread_id": "root",
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
        },
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["is_lower_bound"] is True
    assert any("invalid stream position" in warning for warning in summary["warnings"])


def test_legacy_clean_stream_without_child_sentinel_stays_complete(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        {"type": "turn.completed", "usage": {"input_tokens": 1, "output_tokens": 1}},
    )

    summary = _summary(CodexBackend(), path)

    assert summary["total"] == 0
    assert summary["complete"] is True
    assert summary["warnings"] == []


def test_terminal_turn_failure_can_still_enumerate_every_tool_call(tmp_path):
    path = _write_jsonl(
        tmp_path / "output.jsonl",
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        _item("item.started", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        _item("item.completed", "command", "command_execution", "/bin/bash -lc 'tlapm Foo.tla'"),
        {"type": "turn.failed", "error": {"message": "provider rejected the next request"}},
    )

    summary = _summary(CodexBackend(), path)

    assert (summary["total"], summary["tlaps"]) == (1, 1)
    assert summary["complete"] is True
    assert summary["is_lower_bound"] is False
    assert summary["warnings"] == []


def test_missing_stream_is_unavailable(tmp_path):
    summary = _summary(CodexBackend(), str(tmp_path / "missing.jsonl"))

    assert summary["available"] is False
    assert summary["complete"] is False
    assert summary["is_lower_bound"] is False
    assert any("missing or unreadable" in warning for warning in summary["warnings"])
