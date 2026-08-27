"""Strict manifest-driven proof-completion mode."""

from __future__ import annotations

import json
import pickle
import sys
from unittest.mock import MagicMock

import pytest

from common.proof_completion_contract import BEGIN_AGENT_PROOF, END_AGENT_PROOF, ManifestError
from common.proof_from_scratch_contract import BEGIN_AGENT_HELPERS
from evaluator import runner
from evaluator.backends.agentic import AgenticBackend
from evaluator.modes.proof_completion import ProofCompletion


class _Backend(AgenticBackend):
    name = "copilot"

    def build_command(self, workspace, result_dir):
        return ["fake-agent"]

    def parse_output(self, jsonl_path):
        return "", 0, 100

    def detect_quota_block(self, jsonl_path):
        return None


def _write_module(suite, relative_path, body=""):
    path = suite / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"---- MODULE {path.stem} ----\n{body}====\n", encoding="utf-8")
    return path.resolve()


def _write_task(suite, relative_path, body=""):
    return _write_module(
        suite,
        relative_path,
        (f"{body}THEOREM Target == TRUE\n{BEGIN_AGENT_PROOF}\nPROOF OBVIOUS\n{END_AGENT_PROOF}\n"),
    )


def _write_manifest(suite, manifest):
    suite.mkdir(parents=True, exist_ok=True)
    (suite / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")


def _mode(tmp_path):
    return ProofCompletion(str(tmp_path), "/checker")


def test_strict_mode_discovers_only_manifest_tasks_and_exact_context(tmp_path):
    suite = tmp_path / "proof-completion"
    task_z = _write_task(suite, "Zed/Zed_Target.tla")
    task_a = _write_task(suite, "Alpha/Alpha_Target.tla", "EXTENDS ModelB, ModelA\n")
    context_b = _write_module(suite, "Context/ModelB.tla")
    context_a = _write_module(suite, "Context/ModelA.tla")
    undeclared = _write_task(suite, "Alpha/Undeclared_Target.tla")
    _write_manifest(
        suite,
        {
            "Zed/Zed_Target.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0},
            "Alpha/Alpha_Target.tla": {
                "spec_id": "Fixture.tla",
                "context": ["Context/ModelB.tla", "Context/ModelA.tla"],
                "reference_proof_steps": 0,
            },
        },
    )

    mode = _mode(tmp_path)

    assert mode.read_only_dependencies
    assert mode.canonical_replay_required
    assert mode.get_benchmark_files() == [str(task_a), str(task_z)]
    assert mode.get_dependencies(str(task_a)) == [str(context_b), str(context_a)]
    assert mode.specification_ids() == {
        "Alpha/Alpha_Target.tla": "Fixture.tla",
        "Zed/Zed_Target.tla": "Fixture.tla",
    }
    assert not mode.is_benchmark_file(str(undeclared))
    assert mode.get_benchmark_files("Alpha_Target, Zed/") == [str(task_a), str(task_z)]


def test_strict_mode_is_pickleable_after_discovery(tmp_path):
    suite = tmp_path / "proof-completion"
    task = _write_task(suite, "Example/Example_Target.tla")
    _write_manifest(
        suite, {"Example/Example_Target.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}}
    )
    mode = _mode(tmp_path)
    mode.get_benchmark_files()

    restored = pickle.loads(pickle.dumps(mode))

    assert restored.get_benchmark_files() == [str(task)]
    assert restored.canonical_replay_required


def test_absent_manifest_is_rejected(tmp_path):
    suite = tmp_path / "proof-completion"
    _write_module(suite, "Example/Example_Target.tla", "THEOREM Target == TRUE\nPROOF OBVIOUS\n")

    with pytest.raises(ManifestError, match="missing proof-completion manifest"):
        _mode(tmp_path).get_benchmark_files()


def test_invalid_existing_manifest_fails_closed(tmp_path):
    suite = tmp_path / "proof-completion"
    suite.mkdir()
    (suite / "manifest.json").write_text("{not-json", encoding="utf-8")

    with pytest.raises(ManifestError, match="invalid JSON"):
        _mode(tmp_path).get_benchmark_files()


@pytest.mark.parametrize(
    "marker",
    [
        BEGIN_AGENT_PROOF,
        END_AGENT_PROOF,
        f"{BEGIN_AGENT_PROOF} trailing text",
        BEGIN_AGENT_HELPERS,
    ],
)
def test_marker_without_manifest_is_rejected(tmp_path, marker):
    suite = tmp_path / "proof-completion"
    _write_module(suite, "Example/Example_Target.tla", f"THEOREM Target == TRUE\n{marker}\nPROOF OBVIOUS\n")

    with pytest.raises(ManifestError, match="missing proof-completion manifest"):
        _mode(tmp_path).get_benchmark_files()


def test_marker_in_symlinked_directory_still_requires_manifest(tmp_path):
    suite = tmp_path / "proof-completion"
    linked_suite = tmp_path / "linked"
    _write_task(linked_suite, "Example_Target.tla")
    suite.mkdir()
    (suite / "linked").symlink_to(linked_suite, target_is_directory=True)

    with pytest.raises(ManifestError, match="missing proof-completion manifest"):
        _mode(tmp_path).get_benchmark_files()


def test_manifest_mode_selects_strict_prompts(tmp_path):
    strict_suite = tmp_path / "strict" / "proof-completion"
    _write_task(strict_suite, "Task.tla")
    _write_manifest(strict_suite, {"Task.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}})
    strict = ProofCompletion(str(tmp_path / "strict"), "/checker")

    assert strict.prompt_template_path().endswith("proof-completion-strict.txt")
    assert strict.one_shot_prompt_template_path().endswith("proof-completion-strict-one-shot.txt")


def test_strict_cli_captures_all_inputs_before_backend_setup(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-completion"
    task = _write_task(suite, "Suite/Task.tla", "EXTENDS Model\n")
    model = _write_module(suite, "Context/Model.tla", "Value == TRUE\n")
    _write_manifest(
        suite,
        {"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": ["Context/Model.tla"], "reference_proof_steps": 0}},
    )
    task_source = task.read_bytes()
    model_source = model.read_bytes()
    mode = ProofCompletion(str(benchmark_root), "/checker")
    backend = _Backend()
    captured_items = []

    def mutate_during_backend_setup():
        task.write_text("TAINTED DURING BACKEND SETUP")
        model.write_text("TAINTED DURING BACKEND SETUP")
        return None

    def fake_run(item):
        captured_items.append(item)
        return {
            "benchmark": "Suite/Task.tla",
            "check_verdict": "FAIL",
            "time_secs": 0,
            "input_tokens": 0,
            "output_tokens": 0,
        }

    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "get_mode", lambda *args, **kwargs: mode)
    monkeypatch.setattr(runner, "resolve_paths", lambda: (str(benchmark_root), "/checker"))
    monkeypatch.setattr(backend, "check_auth", mutate_during_backend_setup)
    monkeypatch.setattr(runner, "ensure_tlapm", lambda: None)
    monkeypatch.setattr(runner, "find_tlapm_lib", lambda _tlapm: "/tlapm/lib")
    monkeypatch.setattr(runner, "_run_sany_preflight", lambda **_kwargs: None)
    monkeypatch.setattr(runner, "run_single_benchmark", fake_run)
    monkeypatch.setattr(runner, "update_summary", lambda *args: None)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "tlaps-bench",
            "--mode",
            "proof-completion",
            "--no-container",
            "--output-dir",
            str(tmp_path / "results"),
        ],
    )

    runner.main()

    assert len(captured_items) == 1
    canonical_inputs = captured_items[0].canonical_inputs
    assert canonical_inputs is not None
    assert canonical_inputs.target_bytes == task_source
    assert canonical_inputs.dependencies == (("Model.tla", model_source),)


def test_sany_preflight_failure_stops_before_backend_auth_or_run(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-completion"
    _write_task(suite, "Suite/Task.tla")
    _write_manifest(
        suite,
        {"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": [], "reference_proof_steps": 0}},
    )
    mode = ProofCompletion(str(benchmark_root), "/checker")
    backend = _Backend()
    backend.check_auth = MagicMock(return_value=None)
    run = MagicMock()

    def fail_sany_preflight(**_kwargs):
        raise RuntimeError("SANY unavailable")

    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "get_mode", lambda *args, **kwargs: mode)
    monkeypatch.setattr(runner, "resolve_paths", lambda: (str(benchmark_root), "/checker"))
    monkeypatch.setattr(runner, "ensure_tlapm", lambda: None)
    monkeypatch.setattr(runner, "run_single_benchmark", run)
    monkeypatch.setattr(runner, "_run_sany_preflight", fail_sany_preflight)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "tlaps-bench",
            "--mode",
            "proof-completion",
            "--no-container",
            "--output-dir",
            str(tmp_path / "results"),
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        runner.main()

    assert exc_info.value.code == 2
    backend.check_auth.assert_not_called()
    run.assert_not_called()
