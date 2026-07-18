"""Regression coverage for one-shot orchestration in evaluator.runner."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

from evaluator import runner
from evaluator.backends.litellm_oneshot import LiteLLMOneShotBackend

MODULE = "---- MODULE Example ----\nTHEOREM Target == TRUE\nPROOF OBVIOUS\n====\n"


class _OneShotMode:
    name = "proof-completion"

    def __init__(self, benchmark_root: Path):
        self._benchmark_root = str(benchmark_root)

    def benchmark_dir(self) -> str:
        return self._benchmark_root

    def get_dependencies(self, benchmark_path: str) -> list[str]:
        return []

    def checker_binary_path(self) -> str:
        return "/bin/true"

    def build_one_shot_prompt(self, benchmark_path: str, dependencies: list[str]) -> str:
        return "return one response"


def _make_item(tmp_path: Path, timeout: int = 10) -> tuple[runner.WorkItem, Path]:
    benchmark_root = tmp_path / "benchmark"
    benchmark = benchmark_root / "Suite" / "Example.tla"
    benchmark.parent.mkdir(parents=True)
    benchmark.write_text(MODULE)
    item = runner.WorkItem(
        benchmark_path=str(benchmark),
        output_dir=str(tmp_path / "results"),
        timeout=timeout,
        check_timeout=10,
        backend=LiteLLMOneShotBackend(),
        mode=_OneShotMode(benchmark_root),  # type: ignore[arg-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        infra_retries=0,
    )
    return item, Path(item.output_dir) / "Suite" / "Example"


def _write_clean_response(path: str) -> None:
    events = [
        {"type": "response", "text": MODULE},
        {"type": "usage", "input_tokens": 10, "output_tokens": 5, "model_requests": 1},
        {
            "type": "request_audit",
            "provider": "litellm",
            "litellm_completion_invocations": 1,
            "wire_audited": False,
            "litellm_retries_disabled": True,
            "system_supplied": False,
            "tools_supplied": False,
        },
        {"type": "result", "status": "success", "model_requests": 1},
    ]
    Path(path).write_text("".join(json.dumps(event) + "\n" for event in events))


def _write_provider_timeout(path: str, timeout: int) -> None:
    events = [
        {"type": "usage", "input_tokens": 10, "output_tokens": 5, "model_requests": 1},
        {
            "type": "request_audit",
            "provider": "litellm",
            "litellm_completion_invocations": 1,
            "wire_audited": False,
            "litellm_retries_disabled": True,
            "system_supplied": False,
            "tools_supplied": False,
        },
        {"type": "error", "message": f"provider request timed out after {timeout}s"},
        {"type": "result", "status": "timeout", "model_requests": 1},
    ]
    Path(path).write_text("".join(json.dumps(event) + "\n" for event in events))


def test_rerun_clears_owned_artifacts_and_preserves_unknown_files(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path)
    for name in ("input", "agent", "grading", "continuations"):
        stale_dir = result_dir / name
        stale_dir.mkdir(parents=True, exist_ok=True)
        (stale_dir / "stale.txt").write_text(name)
    (result_dir / "agent" / "solution.tla").write_text("stale solution")
    (result_dir / "grading" / "check.result").write_text("PASS")
    (result_dir / "result.json").write_text('{"stale": true}')
    (result_dir / "review-notes.txt").write_text("keep me")
    unknown_dir = result_dir / "attachments"
    unknown_dir.mkdir()
    (unknown_dir / "evidence.txt").write_text("keep me too")

    def fake_agent(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        _write_clean_response(agent_jsonl)
        result["agent_exit"] = 0

    monkeypatch.setattr(runner, "_run_agent_local", fake_agent)
    monkeypatch.setattr(item.backend, "materialize_solution", lambda *args: False)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("grader must not run"))

    result = runner.run_single_benchmark(item)

    assert result["check_verdict"] == "FAIL"
    assert not (result_dir / "agent" / "solution.tla").exists()
    assert not (result_dir / "grading" / "check.result").exists()
    assert not (result_dir / "continuations").exists()
    assert not any(result_dir.glob("*/stale.txt"))
    assert (result_dir / "input" / "benchmark.tla").read_text() == MODULE
    assert (result_dir / "review-notes.txt").read_text() == "keep me"
    assert (unknown_dir / "evidence.txt").read_text() == "keep me too"
    assert "stale" not in json.loads((result_dir / "result.json").read_text())


def test_quota_skipped_rerun_removes_old_result_json(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path)
    result_dir.mkdir(parents=True)
    (result_dir / "result.json").write_text('{"check_verdict": "PASS"}')
    (result_dir / "review-notes.txt").write_text("keep me")
    monkeypatch.setattr(runner.quota, "wait_for_quota", lambda *args, **kwargs: False)

    result = runner.run_single_benchmark(item)

    assert result["termination_reason"] == "QUOTA_EXHAUSTED"
    assert not (result_dir / "result.json").exists()
    assert (result_dir / "review-notes.txt").read_text() == "keep me"


def test_rerun_refuses_symlinked_result_path(tmp_path):
    item, result_dir = _make_item(tmp_path)
    outside = tmp_path / "outside"
    stale_agent = outside / "agent"
    stale_agent.mkdir(parents=True)
    evidence = stale_agent / "keep.txt"
    evidence.write_text("do not delete")
    result_dir.parent.mkdir(parents=True)
    result_dir.symlink_to(outside, target_is_directory=True)

    with pytest.raises(RuntimeError, match="symlinked benchmark result path"):
        runner.run_single_benchmark(item)

    assert evidence.read_text() == "do not delete"


def test_oneshot_timeout_skips_materialization_and_grading(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path, timeout=37)
    materialize_calls = []
    grader_calls = []

    def fake_agent(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        _write_clean_response(agent_jsonl)
        with Path(agent_jsonl).open("a") as stream:
            stream.write(json.dumps({"type": "error", "message": "earlier provider error"}) + "\n")
        result["agent_exit"] = -1
        result["error"] = "litellm_oneshot timeout after 37s"

    monkeypatch.setattr(runner, "_run_agent_local", fake_agent)
    monkeypatch.setattr(
        item.backend,
        "materialize_solution",
        lambda *args: materialize_calls.append(args) or True,
    )
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: grader_calls.append(args))

    result = runner.run_single_benchmark(item)

    assert result["termination_reason"] == "TIMEOUT"
    assert result["check_verdict"] == "TIMEOUT"
    assert result["error"] == "litellm_oneshot timeout after 37s"
    assert "materialized" not in result
    assert materialize_calls == []
    assert grader_calls == []
    assert not (result_dir / "agent" / "solution.tla").exists()
    assert json.loads((result_dir / "result.json").read_text()) == result


def test_provider_timeout_event_preserves_timeout_and_error(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path, timeout=37)
    materialize_calls = []
    grader_calls = []

    def fake_agent(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        _write_provider_timeout(agent_jsonl, item_.timeout)
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_agent_local", fake_agent)
    monkeypatch.setattr(
        item.backend,
        "materialize_solution",
        lambda *args: materialize_calls.append(args) or True,
    )
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: grader_calls.append(args))

    result = runner.run_single_benchmark(item)

    assert result["termination_reason"] == "TIMEOUT"
    assert result["check_verdict"] == "TIMEOUT"
    assert result["error"] == "provider request timed out after 37s"
    assert materialize_calls == []
    assert grader_calls == []
    assert json.loads((result_dir / "result.json").read_text()) == result


@pytest.mark.parametrize(("timeout", "forwarded"), [(40_000, "40000"), (0, "0"), (-5, "0")])
def test_oneshot_command_forwards_outer_timeout(timeout, forwarded, tmp_path):
    backend = LiteLLMOneShotBackend()

    command = runner._build_agent_command(backend, str(tmp_path), str(tmp_path / "results"), timeout)

    assert command[-2:] == ["--timeout", forwarded]


def test_local_runner_launches_oneshot_with_outer_timeout(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path, timeout=40_000)
    agent_dir = tmp_path / "agent"
    agent_dir.mkdir()
    captured = {}

    class FakeProcess:
        returncode = 0

        def communicate(self, **kwargs):
            captured["communicate"] = kwargs
            return None, ""

    def fake_popen(command, **kwargs):
        captured["command"] = command
        captured["popen"] = kwargs
        return FakeProcess()

    monkeypatch.setattr(runner.subprocess, "Popen", fake_popen)

    result = {}
    runner._run_agent_local(
        item,
        item.backend,
        item.mode,
        str(tmp_path),
        str(agent_dir),
        str(agent_dir / "output.jsonl"),
        "prompt",
        result,
        "/bin/true",
    )

    assert "--timeout 40000" in captured["command"][2]
    assert captured["communicate"]["input"] == "prompt"
    assert result["agent_exit"] == 0


def test_container_runner_launches_oneshot_with_outer_timeout(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path, timeout=40_000)
    agent_dir = tmp_path / "agent"
    agent_dir.mkdir()
    captured = {}

    class FakeContainerRunner:
        def run(self, config, command, stdin_data):
            captured["command"] = command
            captured["stdin_data"] = stdin_data
            proc = subprocess.Popen(
                ["/bin/true"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            return SimpleNamespace(proc=proc)

        def kill(self, _container_run):
            pytest.fail("completed fake container must not be killed")

        def cleanup_credential_tmps(self):
            return None

    monkeypatch.setattr(runner, "ContainerRunner", FakeContainerRunner)

    result = {}
    runner._run_agent_container(
        item,
        item.backend,
        str(tmp_path),
        str(agent_dir),
        str(agent_dir / "output.jsonl"),
        "prompt",
        result,
    )

    assert captured["command"][-2:] == ["--timeout", "40000"]
    assert captured["stdin_data"] == "prompt"
    assert result["agent_exit"] == 0


def test_agentic_command_is_unchanged_by_timeout_forwarding():
    class Backend:
        is_one_shot = False

        def build_command(self, workspace, result_dir):
            return ["agent", workspace, result_dir]

    command = runner._build_agent_command(Backend(), "/workspace", "/results", 300)

    assert command == ["agent", "/workspace", "/results"]
