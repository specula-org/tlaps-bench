"""Codex rollout-tree child usage extraction."""

import json
import sys
from pathlib import Path

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
    }
