"""The committed Proof Completion Core is a valid, stable task cohort."""

import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SUITE = REPO_ROOT / "benchmark" / "proof-completion"


def test_core_list_contains_190_unique_manifest_tasks_from_56_specifications():
    manifest = json.loads((SUITE / "manifest.json").read_text(encoding="utf-8"))
    task_ids = [line.strip() for line in (SUITE / "core.txt").read_text(encoding="utf-8").splitlines() if line.strip()]

    assert len(task_ids) == 190
    assert task_ids == sorted(task_ids)
    assert len(task_ids) == len(set(task_ids))
    assert set(task_ids) <= set(manifest)
    assert all((SUITE / task_id).is_file() for task_id in task_ids)
    assert len({manifest[task_id]["spec_id"] for task_id in task_ids}) == 56
