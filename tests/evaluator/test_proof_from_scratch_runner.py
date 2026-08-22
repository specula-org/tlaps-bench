"""Synthetic end-to-end runner boundary for proof-from-scratch."""

from __future__ import annotations

import hashlib
import json
import os
import sys
from pathlib import Path

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
)
from common.proof_libraries import OfficialLibraryCatalog
from evaluator import runner
from evaluator.backends.agentic import AgenticBackend
from evaluator.backends.base import BackendCapabilities
from evaluator.modes.proof_from_scratch import ProofFromScratch


class _Backend(AgenticBackend):
    name = "copilot"

    def build_command(self, workspace, result_dir):
        return ["fake-agent"]

    def parse_output(self, jsonl_path):
        return "", 0, 100

    def detect_quota_block(self, jsonl_path):
        return None


def _module(name, body=""):
    return f"---- MODULE {name} ----\n{body}====\n"


def _task():
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            BEGIN_AGENT_HELPERS,
            "",
            END_AGENT_HELPERS,
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            "PROOF OBVIOUS",
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def _catalog():
    payload = {"schema_version": 1, "sources": {}, "modules": {}}
    encoded = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()
    return OfficialLibraryCatalog(sources={}, modules={}, digest=hashlib.sha256(encoded).hexdigest())


def _toolchain():
    return {"schema_version": 1, "digest": "locked-toolchain"}


def test_runner_grades_from_pre_agent_canonical_bytes(tmp_path, monkeypatch):
    suite = tmp_path / "benchmark" / "proof-from-scratch"
    task = suite / "Suite" / "Task.tla"
    model = suite / "Context" / "Model.tla"
    sibling = suite / "Suite" / "Sibling_Task.tla"
    unrelated = suite / "Suite" / "UnrelatedDefs.tla"
    task.parent.mkdir(parents=True)
    model.parent.mkdir(parents=True)
    task_source = _task()
    model_source = _module("Model", "Value == TRUE\n")
    task.write_text(task_source)
    model.write_text(model_source)
    sibling.write_text(_module("Sibling_Task", "THEOREM Leak == TRUE\nPROOF OBVIOUS\n"))
    unrelated.write_text(_module("UnrelatedDefs", "Leak == TRUE\n"))
    (suite / "manifest.json").write_text(
        json.dumps({"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": ["Context/Model.tla"]}})
    )

    mode = ProofFromScratch(str(tmp_path / "benchmark"), "/checker")
    backend = _Backend()
    agent_canonical_dirs = []
    grader_canonical_dirs = []

    def fake_prompt(mode_, benchmark_path, dependencies, basename, tlapm_path, tlapm_lib):
        assert Path(benchmark_path).read_text() == task_source
        assert [Path(path).read_text() for path in dependencies] == [model_source]
        return mode_.build_prompt(basename, tlapm_path, tlapm_lib)

    def fake_agent(
        item,
        backend_,
        mode_,
        workspace,
        agent_dir,
        agent_jsonl,
        prompt,
        result,
        checker_bin,
        canonical_dir=None,
    ):
        assert sorted(name for name in os.listdir(workspace) if name.endswith(".tla")) == ["Model.tla", "Task.tla"]
        assert os.stat(os.path.join(workspace, "Model.tla")).st_mode & 0o777 == 0o444
        assert os.stat(os.path.join(workspace, "Task.tla")).st_mode & 0o200
        assert sorted(name for name in os.listdir(canonical_dir) if name.endswith(".tla")) == [
            "Model.tla",
            "Task.tla",
        ]
        agent_canonical_dirs.append(canonical_dir)
        task.write_text(task_source.replace("THEOREM Target == TRUE", "THEOREM Target == FALSE"))
        model.write_text(_module("Model", "Value == FALSE\n"))
        (Path(canonical_dir) / "Model.tla").write_text("TAINTED SELF-CHECK SNAPSHOT")
        with open(agent_jsonl, "w") as f:
            f.write('{"type": "result", "exitCode": 0}\n')
        result["agent_exit"] = 0

    def fake_grader(item, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        assert (Path(canonical_dir) / "Task.tla").read_text() == task_source
        assert (Path(canonical_dir) / "Model.tla").read_text() == model_source
        grader_canonical_dirs.append(canonical_dir)
        result["check_verdict"] = "FAIL"

    monkeypatch.setattr(backend, "build_prompt", fake_prompt)
    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)

    item = runner.WorkItem(
        benchmark_path=str(task),
        output_dir=str(tmp_path / "results"),
        timeout=10,
        check_timeout=10,
        backend=backend,
        mode=mode,
        tlapm_path="/opt/tlapm",
        tlapm_lib="/opt/tlapm/lib",
        infra_retries=0,
        canonical_inputs=runner.CanonicalInputs.capture(str(task), task.name, [str(model)]),
    )
    task.write_text("TAINTED BEFORE THIS WORKER STARTED")
    model.write_text("TAINTED BEFORE THIS WORKER STARTED")

    runner.run_single_benchmark(item)

    input_dir = tmp_path / "results" / "Suite" / "Task" / "input"
    assert sorted(path.name for path in input_dir.iterdir()) == ["Model.tla", "benchmark.tla", "prompt.txt", "skills"]
    assert (input_dir / "benchmark.tla").read_text() == task_source
    assert (input_dir / "Model.tla").read_text() == model_source
    assert BEGIN_AGENT_HELPERS in (input_dir / "prompt.txt").read_text()
    assert list((input_dir / "skills").iterdir()) == []
    assert grader_canonical_dirs[0] != agent_canonical_dirs[0]


def test_cli_captures_all_replay_inputs_before_backend_setup(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-from-scratch"
    task = suite / "Suite" / "Task.tla"
    model = suite / "Context" / "Model.tla"
    task.parent.mkdir(parents=True)
    model.parent.mkdir(parents=True)
    task_source = _task()
    model_source = _module("Model", "Value == TRUE\n")
    task.write_text(task_source)
    model.write_text(model_source)
    (suite / "manifest.json").write_text(
        json.dumps({"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": ["Context/Model.tla"]}})
    )

    mode = ProofFromScratch(str(benchmark_root), "/checker")
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
    monkeypatch.setattr(runner, "_native_verification_environment", lambda: (_catalog(), _toolchain()))
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
            "proof-from-scratch",
            "--no-container",
            "--output-dir",
            str(tmp_path / "results"),
        ],
    )

    runner.main()

    assert len(captured_items) == 1
    canonical_inputs = captured_items[0].canonical_inputs
    assert canonical_inputs is not None
    assert canonical_inputs.target_bytes == task_source.encode()
    assert canonical_inputs.dependencies == (("Model.tla", model_source.encode()),)


def test_proof_from_scratch_tool_free_backend_fails_before_setup(tmp_path, monkeypatch, capsys):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-from-scratch"
    task = suite / "Suite" / "Task.tla"
    model = suite / "Context" / "Model.tla"
    task.parent.mkdir(parents=True)
    model.parent.mkdir(parents=True)
    task.write_text(_task())
    model.write_text(_module("Model"))
    (suite / "manifest.json").write_text(
        json.dumps({"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": ["Context/Model.tla"]}})
    )
    mode = ProofFromScratch(str(benchmark_root), "/checker")
    backend = _Backend()
    backend.name = "tool-free"
    backend.capabilities = BackendCapabilities(workspace_tools=False)
    ensure_image_calls = []

    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "get_mode", lambda *args, **kwargs: mode)
    monkeypatch.setattr(runner, "ensure_image", lambda **kwargs: ensure_image_calls.append(kwargs))
    monkeypatch.setattr(
        sys,
        "argv",
        ["tlaps-bench", "--mode", "proof-from-scratch", "--output-dir", str(tmp_path / "results")],
    )

    with pytest.raises(SystemExit) as exc_info:
        runner.main()

    assert exc_info.value.code == 2
    assert "is tool-free and does not support mode 'proof-from-scratch'" in capsys.readouterr().err
    assert ensure_image_calls == []


def test_container_proof_from_scratch_uses_image_environment(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    suite = benchmark_root / "proof-from-scratch"
    task = suite / "Suite" / "Task.tla"
    model = suite / "Context" / "Model.tla"
    task.parent.mkdir(parents=True)
    model.parent.mkdir(parents=True)
    task.write_text(_task())
    model.write_text(_module("Model"))
    (suite / "manifest.json").write_text(
        json.dumps({"Suite/Task.tla": {"spec_id": "Fixture.tla", "context": ["Context/Model.tla"]}})
    )
    mode = ProofFromScratch(str(benchmark_root), "/checker")
    backend = _Backend()
    captured_items = []
    inspected_images = []

    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "get_mode", lambda *args, **kwargs: mode)
    monkeypatch.setattr(runner, "ensure_image", lambda force=False: "tlaps-bench-base:locked")
    monkeypatch.setattr(
        runner,
        "_container_verification_environment",
        lambda image: (inspected_images.append(image) or _catalog(), _toolchain()),
    )
    monkeypatch.setattr(runner, "scan_official_libraries", lambda: pytest.fail("host libraries were scanned"))
    monkeypatch.setattr(backend, "check_auth", lambda: None)
    monkeypatch.setattr(runner, "_run_preflight", lambda *args: None)
    monkeypatch.setattr(
        runner,
        "run_single_benchmark",
        lambda item: (
            captured_items.append(item)
            or {
                "benchmark": "Suite/Task.tla",
                "check_verdict": "FAIL",
                "time_secs": 0,
                "input_tokens": 0,
                "output_tokens": 0,
            }
        ),
    )
    monkeypatch.setattr(runner, "update_summary", lambda *args: None)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "tlaps-bench",
            "--mode",
            "proof-from-scratch",
            "--skip-preflight",
            "--output-dir",
            str(tmp_path / "results"),
        ],
    )

    runner.main()

    assert inspected_images == ["tlaps-bench-base:locked"]
    assert captured_items[0].container_image == "tlaps-bench-base:locked"
    assert captured_items[0].canonical_inputs.proof_library_catalog == _catalog().to_bytes()
