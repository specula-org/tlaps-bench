"""Guarded legacy and strict manifest-driven proof-completion mode."""

from __future__ import annotations

import json
import pickle
import sys

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
            "Zed/Zed_Target.tla": {"context": []},
            "Alpha/Alpha_Target.tla": {
                "context": ["Context/ModelB.tla", "Context/ModelA.tla"],
            },
        },
    )

    mode = _mode(tmp_path)

    assert mode.uses_strict_contract
    assert mode.read_only_dependencies
    assert mode.canonical_replay_required
    assert mode.get_benchmark_files() == [str(task_a), str(task_z)]
    assert mode.get_dependencies(str(task_a)) == [str(context_b), str(context_a)]
    assert not mode.is_benchmark_file(str(undeclared))
    assert mode.get_benchmark_files("Alpha_Target, Zed/") == [str(task_a), str(task_z)]


def test_strict_mode_is_pickleable_after_discovery(tmp_path):
    suite = tmp_path / "proof-completion"
    task = _write_task(suite, "Example/Example_Target.tla")
    _write_manifest(suite, {"Example/Example_Target.tla": {"context": []}})
    mode = _mode(tmp_path)
    mode.get_benchmark_files()

    restored = pickle.loads(pickle.dumps(mode))

    assert restored.get_benchmark_files() == [str(task)]
    assert restored.canonical_replay_required


def test_absent_manifest_uses_legacy_layout_with_one_warning(tmp_path, capsys):
    suite = tmp_path / "proof-completion"
    task = _write_module(suite, "Example/Example_Target.tla", "THEOREM Target == TRUE\nPROOF OBVIOUS\n")
    dependency = _write_module(suite, "Example/Model.tla")
    mode = _mode(tmp_path)

    assert mode.get_benchmark_files() == [str(task)]
    assert mode.get_dependencies(str(task)) == [str(dependency)]
    assert not mode.read_only_dependencies
    assert not mode.canonical_replay_required

    warning = capsys.readouterr().err
    assert warning.count("using legacy unmarked proof-completion") == 1


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
def test_marker_without_manifest_cannot_downgrade_to_legacy(tmp_path, marker):
    suite = tmp_path / "proof-completion"
    _write_module(suite, "Example/Example_Target.tla", f"THEOREM Target == TRUE\n{marker}\nPROOF OBVIOUS\n")

    with pytest.raises(ManifestError, match="marked task.*cannot use legacy discovery"):
        _mode(tmp_path).get_benchmark_files()


def test_marker_in_symlinked_directory_cannot_downgrade_to_legacy(tmp_path):
    suite = tmp_path / "proof-completion"
    linked_suite = tmp_path / "linked"
    _write_task(linked_suite, "Example_Target.tla")
    suite.mkdir()
    (suite / "linked").symlink_to(linked_suite, target_is_directory=True)

    with pytest.raises(ManifestError, match="marked task.*cannot use legacy discovery"):
        _mode(tmp_path).get_benchmark_files()


def test_strict_and_legacy_modes_select_matching_prompts(tmp_path):
    strict_suite = tmp_path / "strict" / "proof-completion"
    _write_task(strict_suite, "Task.tla")
    _write_manifest(strict_suite, {"Task.tla": {"context": []}})
    legacy_suite = tmp_path / "legacy" / "proof-completion"
    legacy_suite.mkdir(parents=True)

    strict = ProofCompletion(str(tmp_path / "strict"), "/checker")
    legacy = ProofCompletion(str(tmp_path / "legacy"), "/checker")

    assert strict.prompt_template_path().endswith("proof-completion-strict.txt")
    assert strict.one_shot_prompt_template_path().endswith("proof-completion-strict-one-shot.txt")
    assert legacy.prompt_template_path().endswith("proof-completion.txt")
    assert legacy.one_shot_prompt_template_path().endswith("proof-completion-one-shot.txt")


def test_strict_cli_captures_all_inputs_before_backend_setup(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-completion"
    task = _write_task(suite, "Suite/Task.tla", "EXTENDS Model\n")
    model = _write_module(suite, "Context/Model.tla", "Value == TRUE\n")
    _write_manifest(suite, {"Suite/Task.tla": {"context": ["Context/Model.tla"]}})
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
