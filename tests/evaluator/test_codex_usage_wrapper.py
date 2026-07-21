"""Codex rollout-tree child usage extraction."""

import json
import sys
from pathlib import Path

from evaluator.backends.codex_usage_wrapper import collect_child_usage, main


def _meta(
    session_id: str,
    thread_id: str,
    *,
    parent_thread_id: str | None = None,
    forked_from_id: str | None = None,
) -> dict[str, object]:
    payload: dict[str, object] = {"session_id": session_id, "id": thread_id}
    if parent_thread_id is not None:
        payload["parent_thread_id"] = parent_thread_id
    if forked_from_id is not None:
        payload["forked_from_id"] = forked_from_id
    return {"timestamp": "2026-07-28T00:00:00.000Z", "type": "session_meta", "payload": payload}


def _event(event_type: str, **payload: object) -> dict[str, object]:
    return {
        "timestamp": "2026-07-28T00:00:00.000Z",
        "type": "event_msg",
        "payload": {"type": event_type, **payload},
    }


def _tokens(
    input_tokens: int,
    cached_input_tokens: int,
    output_tokens: int,
    reasoning_output_tokens: int,
) -> dict[str, object]:
    return _event(
        "token_count",
        info={
            "total_token_usage": {
                "input_tokens": input_tokens,
                "cached_input_tokens": cached_input_tokens,
                "output_tokens": output_tokens,
                "reasoning_output_tokens": reasoning_output_tokens,
                "total_tokens": input_tokens + output_tokens,
            }
        },
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
) -> Path:
    path = tmp_path / f"rollout-{thread_id}.jsonl"
    _write_rollout(
        path,
        _meta(
            "root",
            thread_id,
            parent_thread_id=parent_thread_id,
            forked_from_id=forked_from_id,
        ),
        *records,
    )
    return path


def _turn(
    turn_id: str,
    usage: tuple[int, int, int, int] | None = None,
    end: str | None = "task_complete",
) -> tuple[dict[str, object], ...]:
    records = [_event("task_started", turn_id=turn_id)]
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
            "output_tokens",
            "reasoning_output_tokens",
        )
    )


def test_nested_forks_subtract_each_immediate_parent_baseline(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (240, 180, 60, 25)))
    child_path = _rollout(
        tmp_path,
        "child",
        # Forked history retains the parent's metadata, lifecycle, and cumulative usage.
        _meta("root", "root"),
        *_turn("root-turn", (240, 180, 60, 25)),
        *_turn("child-turn", (300, 220, 80, 30)),
        parent_thread_id="root",
        forked_from_id="root",
    )
    grandchild_path = _rollout(
        tmp_path,
        "grandchild",
        _meta("root", "child", parent_thread_id="root", forked_from_id="root"),
        *_turn("root-turn", (240, 180, 60, 25)),
        *_turn("child-turn", (300, 220, 80, 30)),
        *_turn("grandchild-turn", (330, 240, 90, 33)),
        parent_thread_id="child",
        forked_from_id="child",
    )

    audit = collect_child_usage("root", (root_path, child_path, grandchild_path))

    assert audit["complete"] is True
    assert audit["warning_codes"] == []
    assert audit["child_count"] == 2
    assert _usage(audit) == (90, 60, 30, 8)


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
    assert _usage(audit) == (15, 5, 7, 2)


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
    assert _usage(audit) == (0, 0, 0, 0)


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
    assert _usage(audit) == (0, 0, 0, 0)


def test_counter_regression_keeps_the_last_safe_usage_prefix(tmp_path):
    root_path = _rollout(tmp_path, "root", *_turn("root-turn", (100, 50, 20, 4)))
    child_path = _rollout(
        tmp_path,
        "child",
        _event("task_started", turn_id="root-turn"),
        _tokens(100, 50, 20, 4),
        _event("task_complete", turn_id="root-turn"),
        _event("task_started", turn_id="child-turn"),
        _tokens(140, 70, 30, 6),
        _tokens(130, 65, 28, 5),
        _event("task_complete", turn_id="child-turn"),
        parent_thread_id="root",
        forked_from_id="root",
    )

    audit = collect_child_usage("root", (root_path, child_path))

    assert audit["complete"] is False
    assert "child_usage_counter_invalid" in audit["warning_codes"]
    assert _usage(audit) == (40, 20, 10, 2)


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
    assert _usage(audit) == (20, 10, 8, 2)


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
    assert _usage(audit) == (20, 10, 8, 2)


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
    assert _usage(audit) == (0, 0, 0, 0)


def test_persisted_child_reference_requires_a_matching_rollout(tmp_path):
    root_path = _rollout(
        tmp_path,
        "root",
        _event("sub_agent_activity", agent_thread_id="missing-child", kind="started"),
    )

    audit = collect_child_usage("root", (root_path,))

    assert audit["complete"] is False
    assert "referenced_child_rollout_missing" in audit["warning_codes"]


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
meta = {"timestamp": "now", "type": "session_meta", "payload": {"session_id": root, "id": root}}
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
        "version": 1,
        "root_thread_id": "root-thread",
        "child_count": 0,
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "complete": True,
        "warning_codes": [],
    }
