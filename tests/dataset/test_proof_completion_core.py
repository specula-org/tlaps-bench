"""The committed Proof Completion Core is a valid, stable task cohort."""

import json
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SUITE = REPO_ROOT / "benchmark" / "proof-completion"

_CORE_STEP_BANDS = ("1-4", "5-12", "13-30", "31-50", "51-100", "101+")


def _step_band(steps: int) -> str:
    if steps <= 4:
        return "1-4"
    if steps <= 12:
        return "5-12"
    if steps <= 30:
        return "13-30"
    if steps <= 50:
        return "31-50"
    if steps <= 100:
        return "51-100"
    return "101+"


def test_core_list_contains_192_unique_manifest_tasks_from_56_specifications():
    manifest = json.loads((SUITE / "manifest.json").read_text(encoding="utf-8"))
    task_ids = [line.strip() for line in (SUITE / "core.txt").read_text(encoding="utf-8").splitlines() if line.strip()]

    assert len(task_ids) == 192
    assert task_ids == sorted(task_ids)
    assert len(task_ids) == len(set(task_ids))
    assert set(task_ids) <= set(manifest)
    assert all((SUITE / task_id).is_file() for task_id in task_ids)
    assert len({manifest[task_id]["spec_id"] for task_id in task_ids}) == 56


def test_core_tasks_expose_reference_proof_steps_for_website_complexity_bands():
    manifest = json.loads((SUITE / "manifest.json").read_text(encoding="utf-8"))
    task_ids = [line.strip() for line in (SUITE / "core.txt").read_text(encoding="utf-8").splitlines() if line.strip()]

    steps_by_task = {}
    for task_id in task_ids:
        entry = manifest[task_id]
        assert set(entry) == {"spec_id", "context", "reference_proof_steps"}, task_id
        steps = entry["reference_proof_steps"]
        assert type(steps) is int and steps > 0, f"Core task {task_id} must have a positive step count, got {steps!r}"
        steps_by_task[task_id] = steps

    bands = Counter(_step_band(steps) for steps in steps_by_task.values())
    assert set(bands) == set(_CORE_STEP_BANDS)
    assert sum(bands.values()) == 192
