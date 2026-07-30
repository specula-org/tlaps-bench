"""Manifest-driven proof-from-scratch evaluator mode."""

from __future__ import annotations

import json
import pickle

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
    ManifestError,
)
from evaluator.modes.proof_completion import ProofCompletion
from evaluator.modes.proof_from_scratch import ProofFromScratch


def _write_module(suite, relative_path, body=""):
    path = suite / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"---- MODULE {path.stem} ----\n{body}====\n", encoding="utf-8")
    return path.resolve()


def _write_task(suite, relative_path, body=""):
    marked_body = (
        f"{body}"
        f"{BEGIN_AGENT_HELPERS}\n"
        f"{END_AGENT_HELPERS}\n"
        "THEOREM Target == TRUE\n"
        f"{BEGIN_AGENT_PROOF}\n"
        "PROOF OBVIOUS\n"
        f"{END_AGENT_PROOF}\n"
    )
    return _write_module(suite, relative_path, marked_body)


def _write_manifest(suite, manifest):
    suite.mkdir(parents=True, exist_ok=True)
    (suite / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")


def _mode(tmp_path):
    return ProofFromScratch(str(tmp_path), "/checker")


def test_unmarked_proof_completion_keeps_legacy_dependency_permissions(tmp_path):
    (tmp_path / "proof-completion").mkdir()

    assert ProofFromScratch.read_only_dependencies is True
    assert ProofCompletion(str(tmp_path), "/checker").read_only_dependencies is False


def test_discovers_only_sorted_manifest_tasks(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    target_z = _write_task(suite, "Zed/Zed_Target.tla")
    target_a = _write_task(suite, "Alpha/Alpha_Target.tla")
    _write_module(suite, "Alpha/Undeclared_Theorem.tla", "THEOREM Leaked == TRUE\n")
    _write_manifest(
        suite,
        {
            "Zed/Zed_Target.tla": {"context": []},
            "Alpha/Alpha_Target.tla": {"context": []},
        },
    )

    mode = _mode(tmp_path)

    assert mode.get_benchmark_files() == [str(target_a), str(target_z)]
    assert mode.is_benchmark_file(str(target_a))
    assert not mode.is_benchmark_file(str(suite / "Alpha/Undeclared_Theorem.tla"))


def test_filters_manifest_tasks_with_existing_comma_separated_substrings(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    target_a = _write_task(suite, "Alpha/Alpha_Target.tla")
    target_b = _write_task(suite, "Beta/Beta_Target.tla")
    target_c = _write_task(suite, "Gamma/Gamma_Target.tla")
    _write_manifest(
        suite,
        {
            "Alpha/Alpha_Target.tla": {"context": []},
            "Beta/Beta_Target.tla": {"context": []},
            "Gamma/Gamma_Target.tla": {"context": []},
        },
    )

    mode = _mode(tmp_path)

    assert mode.get_benchmark_files("Alpha_Target, Gamma/") == [str(target_a), str(target_c)]
    assert mode.get_benchmark_files("missing,") == []
    assert str(target_b) not in mode.get_benchmark_files("Alpha_Target, Gamma/")


def test_returns_only_manifest_context_in_declared_order(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    target = _write_task(suite, "Example/Example_Target.tla")
    context_b = _write_module(suite, "Context/ModelB.tla")
    context_a = _write_module(suite, "Context/ModelA.tla")
    _write_module(suite, "Example/UnrelatedDefs.tla")
    _write_manifest(
        suite,
        {
            "Example/Example_Target.tla": {
                "context": ["Context/ModelB.tla", "Context/ModelA.tla"],
            }
        },
    )

    assert _mode(tmp_path).get_dependencies(str(target)) == [str(context_b), str(context_a)]


def test_rejects_dependency_lookup_for_undeclared_file(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    _write_task(suite, "Example/Example_Target.tla")
    undeclared = _write_module(suite, "Example/Other_Target.tla")
    _write_manifest(suite, {"Example/Example_Target.tla": {"context": []}})

    with pytest.raises(ValueError, match="is not declared"):
        _mode(tmp_path).get_dependencies(str(undeclared))


def test_missing_manifest_fails_closed_during_discovery(tmp_path):
    (tmp_path / "proof-from-scratch").mkdir()

    with pytest.raises(ManifestError, match="missing proof-from-scratch manifest"):
        _mode(tmp_path).get_benchmark_files()


def test_mode_remains_pickleable_after_manifest_discovery(tmp_path):
    suite = tmp_path / "proof-from-scratch"
    target = _write_task(suite, "Example/Example_Target.tla")
    context = _write_module(suite, "Context/Model.tla")
    _write_manifest(
        suite,
        {"Example/Example_Target.tla": {"context": ["Context/Model.tla"]}},
    )
    mode = _mode(tmp_path)
    mode.get_benchmark_files()

    restored = pickle.loads(pickle.dumps(mode))

    assert restored.get_benchmark_files() == [str(target)]
    assert restored.get_dependencies(str(target)) == [str(context)]
