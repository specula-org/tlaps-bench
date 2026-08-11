"""Stable source-specification identities in generated manifests."""

import json
from pathlib import Path

import pytest

from common.task_contract import ManifestError, load_manifest_specification_ids
from dataset.specification_identity import source_spec_id

REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = REPO_ROOT / "source"


def test_source_spec_id_preserves_the_source_relative_path(tmp_path):
    source_root = tmp_path / "source"
    nested = source_root / "Example" / "variant" / "Spec.tla"

    assert source_spec_id(str(nested), str(source_root)) == "Example/variant/Spec.tla"
    assert source_spec_id(str(tmp_path / "external" / "Spec.tla"), str(source_root)) == "Spec.tla"


def test_identity_loader_rejects_a_manifest_entry_without_a_mapping(tmp_path):
    suite = tmp_path / "proof-completion"
    suite.mkdir()
    (suite / "manifest.json").write_text(json.dumps({"Task.tla": {"context": []}}), encoding="utf-8")

    with pytest.raises(ManifestError, match="exactly 'spec_id', 'context', and 'reference_proof_steps'"):
        load_manifest_specification_ids(suite, suite_name="proof-completion")


def test_current_manifests_map_every_task_to_an_existing_source_specification():
    manifests = {}
    for mode in ("proof-completion", "proof-from-scratch"):
        path = REPO_ROOT / "benchmark" / mode / "manifest.json"
        manifest = json.loads(path.read_text(encoding="utf-8"))
        manifests[mode] = manifest
        assert manifest
        expected_keys = (
            {"spec_id", "context", "reference_proof_steps"} if mode == "proof-completion" else {"spec_id", "context"}
        )
        for task_id, entry in manifest.items():
            assert set(entry) == expected_keys, task_id
            assert (SOURCE_ROOT / entry["spec_id"]).is_file(), task_id
            if mode == "proof-completion":
                steps = entry["reference_proof_steps"]
                assert steps is None or (isinstance(steps, int) and not isinstance(steps, bool) and steps >= 0)

    shared_tasks = set(manifests["proof-completion"]) & set(manifests["proof-from-scratch"])
    assert shared_tasks
    for task_id in shared_tasks:
        assert manifests["proof-completion"][task_id]["spec_id"] == manifests["proof-from-scratch"][task_id]["spec_id"]
