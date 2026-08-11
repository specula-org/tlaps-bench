"""Validate exact task coverage and classifications in batch audit JSON files."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1
REPORT_PATTERN = re.compile(r"^batch-(\d+)\.json$")

AXES: dict[str, set[str]] = {
    "task_integrity": {"PASS", "NEEDS_REVIEW", "CONFIRMED_FAULT"},
    "provability": {"CHECKER_PROVED", "SUPPORTED", "NOT_DEMONSTRATED", "DISPROVED"},
    "leakage": {"NONE_FOUND", "CANDIDATE", "CONFIRMED"},
    "difficulty": {"INFORMATIVE", "TRIVIAL_CANDIDATE", "NOT_ASSESSED"},
    "source_reference": {
        "PASSES",
        "OMITS_STEPS",
        "FAILS_CURRENT_TLAPM",
        "TIMEOUT",
        "MISSING",
        "NOT_ASSESSED",
    },
    "run_alignment": {"CURRENT", "STALE", "MISSING", "NOT_ASSESSED"},
    "model_outcome": {
        "PASS",
        "SANY_SYNTAX",
        "TLAPS_UNPROVED",
        "INFRA",
        "PROTOCOL",
        "RESOURCE",
        "UNKNOWN",
        "NOT_ASSESSED",
    },
}


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"Cannot read {path}: {error}") from error


def write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", required=True, help="Inventory JSON from build_audit_inventory.py.")
    parser.add_argument("--reports-dir", required=True, help="Directory that contains batch-<NN>.json files.")
    parser.add_argument("--summary-output", help="Optional output path for the validated summary JSON.")
    return parser.parse_args()


def validate_report_task(
    record: Any,
    *,
    path: Path,
    expected_by_id: dict[str, dict[str, Any]],
    declared_batch: int,
    seen: dict[str, Path],
    errors: list[str],
) -> None:
    location = f"{path} task entry"
    if not isinstance(record, dict):
        errors.append(f"{location} is not an object.")
        return

    task_id = record.get("task_id")
    if not isinstance(task_id, str):
        errors.append(f"{location} has no string task_id.")
        return
    if task_id not in expected_by_id:
        errors.append(f"{path} contains unknown task ID {task_id!r}.")
        return
    if task_id in seen:
        errors.append(f"Task {task_id} appears in both {seen[task_id]} and {path}.")
        return
    seen[task_id] = path

    expected = expected_by_id[task_id]
    if declared_batch != expected["batch"]:
        errors.append(f"Task {task_id} is in batch {declared_batch}, but inventory assigns batch {expected['batch']}.")
    if record.get("ordinal") != expected["ordinal"]:
        errors.append(f"Task {task_id} has ordinal {record.get('ordinal')!r}; expected {expected['ordinal']}.")

    for field, allowed in AXES.items():
        value = record.get(field)
        if value not in allowed:
            errors.append(f"Task {task_id} has invalid {field} {value!r}. Allowed: {', '.join(sorted(allowed))}.")

    summary = record.get("summary")
    if not isinstance(summary, str) or not summary.strip():
        errors.append(f"Task {task_id} has no non-empty summary.")
    evidence = record.get("evidence")
    if (
        not isinstance(evidence, list)
        or not evidence
        or not all(isinstance(item, str) and item.strip() for item in evidence)
    ):
        errors.append(f"Task {task_id} must contain a non-empty evidence string list.")
    commands = record.get("commands", [])
    if not isinstance(commands, list) or not all(isinstance(item, str) for item in commands):
        errors.append(f"Task {task_id} commands must be a string list.")

    integrity = record.get("task_integrity")
    provability = record.get("provability")
    leakage = record.get("leakage")
    if provability == "DISPROVED" and integrity != "CONFIRMED_FAULT":
        errors.append(f"Task {task_id} is DISPROVED but is not a CONFIRMED_FAULT.")
    if leakage == "CANDIDATE" and integrity != "NEEDS_REVIEW":
        errors.append(f"Task {task_id} has a leakage CANDIDATE but is not NEEDS_REVIEW.")
    if leakage == "CONFIRMED" and integrity != "CONFIRMED_FAULT":
        errors.append(f"Task {task_id} has CONFIRMED leakage but is not a CONFIRMED_FAULT.")


def main() -> int:
    args = parse_args()
    inventory_path = Path(args.inventory).resolve()
    reports_dir = Path(args.reports_dir).resolve()
    errors: list[str] = []

    try:
        inventory = read_json(inventory_path)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if not isinstance(inventory, dict) or inventory.get("schema_version") != SCHEMA_VERSION:
        print(f"error: Unsupported inventory schema in {inventory_path}", file=sys.stderr)
        return 2
    inventory_tasks = inventory.get("tasks")
    if not isinstance(inventory_tasks, list):
        print(f"error: Inventory {inventory_path} has no task list.", file=sys.stderr)
        return 2

    expected_by_id: dict[str, dict[str, Any]] = {}
    for item in inventory_tasks:
        if not isinstance(item, dict) or not isinstance(item.get("task_id"), str):
            errors.append("Inventory contains an invalid task record.")
            continue
        expected_by_id[item["task_id"]] = item

    if not reports_dir.is_dir():
        print(f"error: Reports directory does not exist: {reports_dir}", file=sys.stderr)
        return 2

    report_files: list[tuple[int, Path]] = []
    for path in sorted(reports_dir.glob("batch-*.json")):
        match = REPORT_PATTERN.match(path.name)
        if match:
            report_files.append((int(match.group(1)), path))

    expected_batches = set(range(1, int(inventory.get("batch_count", 0)) + 1))
    actual_batches = {batch for batch, _ in report_files}
    missing_batches = sorted(expected_batches - actual_batches)
    extra_batches = sorted(actual_batches - expected_batches)
    if missing_batches:
        errors.append(f"Missing batch report files: {missing_batches}")
    if extra_batches:
        errors.append(f"Unexpected batch report files: {extra_batches}")
    if len(actual_batches) != len(report_files):
        errors.append("Two report file names resolve to the same numeric batch.")

    seen: dict[str, Path] = {}
    records: list[dict[str, Any]] = []
    for filename_batch, path in report_files:
        try:
            report = read_json(path)
        except ValueError as error:
            errors.append(str(error))
            continue
        if not isinstance(report, dict):
            errors.append(f"{path} is not a JSON object.")
            continue
        if report.get("schema_version") != SCHEMA_VERSION:
            errors.append(f"{path} has an unsupported schema_version.")
        declared_batch = report.get("batch")
        if declared_batch != filename_batch:
            errors.append(f"{path} declares batch {declared_batch!r}; its file name declares {filename_batch}.")
        tasks = report.get("tasks")
        if not isinstance(tasks, list):
            errors.append(f"{path} has no task list.")
            continue
        for record in tasks:
            validate_report_task(
                record,
                path=path,
                expected_by_id=expected_by_id,
                declared_batch=filename_batch,
                seen=seen,
                errors=errors,
            )
            if isinstance(record, dict) and record.get("task_id") in expected_by_id:
                records.append(record)

    missing_tasks = [task_id for task_id in expected_by_id if task_id not in seen]
    if missing_tasks:
        errors.append(f"Missing task results: {', '.join(missing_tasks)}")

    if errors:
        print("Audit coverage validation failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    ordered_records = sorted(records, key=lambda item: expected_by_id[item["task_id"]]["ordinal"])
    counts: dict[str, dict[str, int]] = {}
    for field in AXES:
        counter = Counter(record[field] for record in ordered_records)
        counts[field] = dict(sorted(counter.items()))

    summary = {
        "schema_version": SCHEMA_VERSION,
        "inventory": str(inventory_path),
        "git_commit": inventory.get("git_commit"),
        "mode": inventory.get("mode"),
        "task_list": inventory.get("task_list"),
        "task_count": len(ordered_records),
        "batch_count": len(report_files),
        "coverage_complete": True,
        "counts": counts,
    }
    if args.summary_output:
        write_json_atomic(Path(args.summary_output).resolve(), summary)

    print(f"Coverage complete: {len(ordered_records)} tasks in {len(report_files)} batches")
    for field, values in counts.items():
        rendered = ", ".join(f"{value}={count}" for value, count in values.items())
        print(f"{field}: {rendered}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
