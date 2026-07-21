"""Stream ``codex exec`` JSONL and append a sanitized child-thread usage audit.

Codex's public ``turn.completed`` event reports only the primary thread. Child
threads persist native cumulative token counters in their rollout files, so this
wrapper reads those files after Codex exits and emits only aggregate token counts
and lifecycle completeness. Prompts and other rollout content never leave the
Codex state directory.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path

CODEX_CHILD_USAGE_EVENT = "tlaps.codex_child_usage"
CODEX_CHILD_USAGE_START_EVENT = "tlaps.codex_child_usage.started"
CODEX_CHILD_USAGE_VERSION = 1

_TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
)
_TURN_STARTED_TYPES = frozenset({"task_started", "turn_started"})
_TURN_COMPLETED_TYPES = frozenset({"task_complete", "turn_complete"})


@dataclass(frozen=True)
class _TokenTotals:
    input_tokens: int = 0
    cached_input_tokens: int = 0
    output_tokens: int = 0
    reasoning_output_tokens: int = 0

    def __add__(self, other: _TokenTotals) -> _TokenTotals:
        return _TokenTotals(**{field: getattr(self, field) + getattr(other, field) for field in _TOKEN_FIELDS})

    def delta_from(self, baseline: _TokenTotals) -> _TokenTotals | None:
        values = {field: getattr(self, field) - getattr(baseline, field) for field in _TOKEN_FIELDS}
        if any(value < 0 for value in values.values()):
            return None
        return _TokenTotals(**values)

    def to_dict(self) -> dict[str, int]:
        return {field: getattr(self, field) for field in _TOKEN_FIELDS}


@dataclass(frozen=True)
class _TimelineItem:
    index: int
    kind: str
    turn_id: str | None = None
    totals: _TokenTotals | None = None


@dataclass(frozen=True)
class _RolloutMeta:
    session_id: str
    thread_id: str
    parent_thread_id: str | None
    forked_from_id: str | None


@dataclass(frozen=True)
class _UsageRollout:
    meta: _RolloutMeta
    timeline: tuple[_TimelineItem, ...]
    referenced_child_ids: frozenset[str]
    invalid_indexes: tuple[int, ...]

    @property
    def turn_ids(self) -> frozenset[str]:
        return frozenset(item.turn_id for item in self.timeline if item.kind == "started" and item.turn_id)

    @property
    def structurally_complete(self) -> bool:
        return not self.invalid_indexes


def _strict_token(value: object) -> int | None:
    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else None


def _parse_totals(value: object) -> _TokenTotals | None:
    if not isinstance(value, dict):
        return None
    parsed = {field: _strict_token(value.get(field)) for field in _TOKEN_FIELDS}
    if any(token is None for token in parsed.values()):
        return None
    totals = _TokenTotals(**parsed)  # type: ignore[arg-type]
    if totals.cached_input_tokens > totals.input_tokens:
        return None
    if totals.reasoning_output_tokens > totals.output_tokens:
        return None
    return totals


def _parse_meta_record(value: object) -> _RolloutMeta | None:
    if not isinstance(value, dict) or value.get("type") != "session_meta":
        return None
    payload = value.get("payload")
    if not isinstance(payload, dict):
        return None
    session_id = payload.get("session_id")
    thread_id = payload.get("id")
    parent_thread_id = payload.get("parent_thread_id")
    forked_from_id = payload.get("forked_from_id")
    if not isinstance(session_id, str) or not session_id or not isinstance(thread_id, str) or not thread_id:
        return None
    if parent_thread_id is not None and (not isinstance(parent_thread_id, str) or not parent_thread_id):
        return None
    if forked_from_id is not None and (not isinstance(forked_from_id, str) or not forked_from_id):
        return None
    return _RolloutMeta(
        session_id=session_id,
        thread_id=thread_id,
        parent_thread_id=parent_thread_id,
        forked_from_id=forked_from_id,
    )


def _read_usage_rollout(path: Path) -> _UsageRollout | None:
    meta: _RolloutMeta | None = None
    timeline: list[_TimelineItem] = []
    referenced_child_ids: set[str] = set()
    invalid_indexes: list[int] = []
    try:
        with path.open(encoding="utf-8") as rollout:
            for index, raw in enumerate(rollout):
                if not raw.strip():
                    continue
                try:
                    record = json.loads(raw)
                except json.JSONDecodeError:
                    if index == 0:
                        return None
                    invalid_indexes.append(index)
                    continue
                if not isinstance(record, dict):
                    if index == 0:
                        return None
                    invalid_indexes.append(index)
                    continue
                if index == 0:
                    meta = _parse_meta_record(record)
                    if meta is None:
                        return None
                    continue
                if record.get("type") != "event_msg":
                    continue
                payload = record.get("payload")
                if not isinstance(payload, dict):
                    invalid_indexes.append(index)
                    continue
                event_type = payload.get("type")
                if event_type == "token_count":
                    info = payload.get("info")
                    if info is None:
                        continue
                    totals = _parse_totals(info.get("total_token_usage") if isinstance(info, dict) else None)
                    if totals is None:
                        invalid_indexes.append(index)
                    else:
                        timeline.append(_TimelineItem(index=index, kind="tokens", totals=totals))
                elif event_type in _TURN_STARTED_TYPES:
                    turn_id = payload.get("turn_id")
                    if isinstance(turn_id, str) and turn_id:
                        timeline.append(_TimelineItem(index=index, kind="started", turn_id=turn_id))
                    else:
                        invalid_indexes.append(index)
                elif event_type in _TURN_COMPLETED_TYPES:
                    turn_id = payload.get("turn_id")
                    if isinstance(turn_id, str) and turn_id:
                        timeline.append(_TimelineItem(index=index, kind="completed", turn_id=turn_id))
                    else:
                        invalid_indexes.append(index)
                elif event_type == "turn_aborted":
                    turn_id = payload.get("turn_id")
                    if turn_id is None or (isinstance(turn_id, str) and turn_id):
                        timeline.append(_TimelineItem(index=index, kind="aborted", turn_id=turn_id))
                    else:
                        invalid_indexes.append(index)
                elif event_type == "sub_agent_activity":
                    child_thread_id = payload.get("agent_thread_id")
                    if isinstance(child_thread_id, str) and child_thread_id:
                        referenced_child_ids.add(child_thread_id)
                    else:
                        invalid_indexes.append(index)
    except (OSError, UnicodeError):
        invalid_indexes.append(len(timeline) + 1)
    if meta is None:
        return None
    return _UsageRollout(
        meta=meta,
        timeline=tuple(timeline),
        referenced_child_ids=frozenset(referenced_child_ids),
        invalid_indexes=tuple(invalid_indexes),
    )


def _analyze_child(child: _UsageRollout, parent: _UsageRollout | None) -> tuple[_TokenTotals, set[str]]:
    warning_codes: set[str] = set()
    usage_change_indexes: set[int] = set()
    inherited_turn_ids: frozenset[str] = frozenset()
    forked = child.meta.forked_from_id is not None
    if forked:
        if (
            parent is None
            or not parent.structurally_complete
            or child.meta.forked_from_id != child.meta.parent_thread_id
        ):
            return _TokenTotals(), {"fork_baseline_unavailable"}
        inherited_turn_ids = parent.turn_ids

    own_starts = [item for item in child.timeline if item.kind == "started" and item.turn_id not in inherited_turn_ids]

    boundary = own_starts[0].index if own_starts else 0
    baselines = [
        item for item in child.timeline if item.kind == "tokens" and item.index < boundary and item.totals is not None
    ]
    baseline = baselines[-1].totals if baselines else _TokenTotals()
    assert baseline is not None
    inherited_counter_invalid = False
    previous_inherited = _TokenTotals()
    for item in baselines:
        assert item.totals is not None
        if item.totals.delta_from(previous_inherited) is None:
            inherited_counter_invalid = True
            break
        previous_inherited = item.totals
    if forked and not own_starts:
        safe_delta = _TokenTotals()
    elif forked and (inherited_counter_invalid or any(index < boundary for index in child.invalid_indexes)):
        warning_codes.add("fork_baseline_unavailable")
        safe_delta = _TokenTotals()
    else:
        previous = baseline
        for item in child.timeline:
            if item.kind != "tokens" or item.index < boundary or item.totals is None:
                continue
            if item.totals.delta_from(previous) is None:
                warning_codes.add("child_usage_counter_invalid")
                break
            if item.totals != previous:
                usage_change_indexes.add(item.index)
            previous = item.totals
        safe_delta = previous.delta_from(baseline) or _TokenTotals()

    active_turns: set[str] = set()
    finished_turns: set[str] = set()
    turns_with_usage: set[str] = set()
    for item in child.timeline:
        if item.index < boundary or item.turn_id in inherited_turn_ids:
            continue
        if item.kind == "started" and item.turn_id:
            if active_turns or item.turn_id in finished_turns:
                warning_codes.add("child_lifecycle_invalid")
            active_turns.add(item.turn_id)
        elif item.kind == "tokens" and item.index in usage_change_indexes:
            if active_turns:
                turns_with_usage.update(active_turns)
            else:
                warning_codes.add("child_lifecycle_invalid")
        elif item.kind == "completed" and item.turn_id:
            if item.turn_id not in active_turns:
                warning_codes.add("child_lifecycle_invalid")
            elif item.turn_id not in turns_with_usage:
                warning_codes.add("child_usage_missing")
            active_turns.discard(item.turn_id)
            finished_turns.add(item.turn_id)
        elif item.kind == "aborted":
            warning_codes.add("child_lifecycle_invalid")
            if item.turn_id:
                active_turns.discard(item.turn_id)
    if active_turns or (not own_starts and not forked):
        warning_codes.add("child_lifecycle_invalid")
    if not child.structurally_complete:
        warning_codes.add("rollout_invalid")

    return safe_delta, warning_codes


def _belongs_to_tree(thread_id: str, root_thread_id: str, by_thread: dict[str, _UsageRollout]) -> bool:
    seen: set[str] = set()
    while thread_id != root_thread_id:
        if thread_id in seen:
            return False
        seen.add(thread_id)
        rollout = by_thread.get(thread_id)
        if rollout is None or rollout.meta.parent_thread_id is None:
            return False
        thread_id = rollout.meta.parent_thread_id
    return True


def collect_child_usage(root_thread_id: str, candidate_paths: Iterable[Path]) -> dict[str, object]:
    """Build a sanitized audit for one newly-created Codex session tree."""

    warning_codes: set[str] = set()
    by_thread: dict[str, _UsageRollout] = {}
    duplicate_thread_ids: set[str] = set()
    for path in sorted(candidate_paths):
        rollout = _read_usage_rollout(path)
        if rollout is None:
            warning_codes.add("new_rollout_metadata_invalid")
        elif rollout.meta.session_id != root_thread_id or rollout.meta.thread_id in duplicate_thread_ids:
            continue
        elif rollout.meta.thread_id in by_thread:
            warning_codes.add("duplicate_thread_rollout")
            by_thread.pop(rollout.meta.thread_id)
            duplicate_thread_ids.add(rollout.meta.thread_id)
        else:
            by_thread[rollout.meta.thread_id] = rollout

    root = by_thread.get(root_thread_id)
    if (
        root is None
        or root.meta.session_id != root.meta.thread_id
        or root.meta.parent_thread_id is not None
        or root.meta.forked_from_id is not None
    ):
        warning_codes.add("root_rollout_missing")
    elif not root.structurally_complete:
        warning_codes.add("rollout_invalid")

    known_thread_ids = set(by_thread)
    if any(rollout.referenced_child_ids - known_thread_ids for rollout in by_thread.values()):
        warning_codes.add("referenced_child_rollout_missing")

    child_count = 0
    totals = _TokenTotals()
    for thread_id, rollout in sorted(by_thread.items()):
        if thread_id == root_thread_id:
            continue
        child_count += 1
        if not _belongs_to_tree(thread_id, root_thread_id, by_thread):
            warning_codes.add("thread_tree_invalid")
            continue
        parent_thread_id = rollout.meta.parent_thread_id
        child_totals, child_warnings = _analyze_child(
            rollout, by_thread.get(parent_thread_id) if parent_thread_id else None
        )
        totals += child_totals
        warning_codes.update(child_warnings)

    return {
        "type": CODEX_CHILD_USAGE_EVENT,
        "version": CODEX_CHILD_USAGE_VERSION,
        "root_thread_id": root_thread_id,
        "child_count": child_count,
        **totals.to_dict(),
        "complete": not warning_codes,
        "warning_codes": sorted(warning_codes),
    }


def _dates_between(first: date, last: date) -> Iterable[date]:
    current = first
    while current <= last:
        yield current
        current += timedelta(days=1)


def _rollout_paths(sessions_dir: Path, first: date, last: date) -> set[Path]:
    paths: set[Path] = set()
    for day in _dates_between(first, last):
        day_dir = sessions_dir / str(day.year) / f"{day.month:02d}" / f"{day.day:02d}"
        paths.update(day_dir.glob("rollout-*.jsonl"))
    return paths


def _codex_home() -> Path:
    configured = os.environ.get("CODEX_HOME")
    return Path(configured) if configured else Path.home() / ".codex"


def _stream_codex(command: Sequence[str]) -> tuple[int, str | None, bool]:
    try:
        process = subprocess.Popen(
            command,
            stdin=None,
            stdout=subprocess.PIPE,
            stderr=None,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
        )
    except OSError as exc:
        print(f"failed to launch Codex: {type(exc).__name__}", file=sys.stderr)
        return 127, None, False

    root_thread_id: str | None = None
    conflicting_root = False
    ended_with_newline = True
    assert process.stdout is not None
    for raw in process.stdout:
        sys.stdout.write(raw)
        sys.stdout.flush()
        ended_with_newline = raw.endswith("\n")
        try:
            event = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(event, dict) or event.get("type") != "thread.started":
            continue
        candidate = event.get("thread_id")
        if not isinstance(candidate, str) or not candidate:
            continue
        if root_thread_id is None:
            root_thread_id = candidate
        elif candidate != root_thread_id:
            conflicting_root = True
    return_code = process.wait()
    if not ended_with_newline:
        sys.stdout.write("\n")
    return return_code, root_thread_id, conflicting_root


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a Codex command is required after --")

    sessions_dir = _codex_home() / "sessions"
    started = datetime.now().astimezone()
    existing_paths = _rollout_paths(sessions_dir, started.date(), started.date())
    print(
        json.dumps(
            {"type": CODEX_CHILD_USAGE_START_EVENT, "version": CODEX_CHILD_USAGE_VERSION},
            separators=(",", ":"),
            sort_keys=True,
        ),
        flush=True,
    )
    return_code, root_thread_id, conflicting_root = _stream_codex(command)
    ended = datetime.now().astimezone()

    if root_thread_id is not None:
        try:
            candidate_paths = _rollout_paths(sessions_dir, started.date(), ended.date()) - existing_paths
            audit = collect_child_usage(root_thread_id, candidate_paths)
            if conflicting_root:
                audit["complete"] = False
                warning_codes = audit.get("warning_codes")
                if isinstance(warning_codes, list):
                    warning_codes.append("root_thread_id_conflict")
                    warning_codes.sort()
        except Exception:
            audit = {
                "type": CODEX_CHILD_USAGE_EVENT,
                "version": CODEX_CHILD_USAGE_VERSION,
                "root_thread_id": root_thread_id,
                "child_count": 0,
                **_TokenTotals().to_dict(),
                "complete": False,
                "warning_codes": ["audit_failed"],
            }
        print(json.dumps(audit, separators=(",", ":"), sort_keys=True), flush=True)
    return return_code if return_code >= 0 else 128 - return_code


if __name__ == "__main__":
    raise SystemExit(main())
