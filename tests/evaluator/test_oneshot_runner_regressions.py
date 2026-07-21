"""Regression coverage for one-shot orchestration in evaluator.runner."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace

import pytest

from evaluator import runner
from evaluator.backends.agentic import AgenticBackend
from evaluator.backends.copilot_oneshot import CopilotOneShotBackend
from evaluator.backends.litellm_oneshot import LiteLLMOneShotBackend
from evaluator.backends.oneshot_runner import StrictCopilotRequestHandler

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
            "model_requests": 1,
            "request_attempts": 1,
            "blocked_requests": 0,
            "system_prompt_present": False,
            "tools_present": False,
            "retries_enabled": False,
            "audit_scope": "adapter",
            "contract_ok": True,
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
            "model_requests": 1,
            "request_attempts": 1,
            "blocked_requests": 0,
            "system_prompt_present": False,
            "tools_present": False,
            "retries_enabled": False,
            "audit_scope": "adapter",
            "contract_ok": True,
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

    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
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

    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
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

    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
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


def test_copilot_command_receives_absolute_deadline(tmp_path):
    backend = CopilotOneShotBackend()
    deadline = time.time() + 40_000

    command = runner._build_backend_command(backend, str(tmp_path), str(tmp_path / "results"), deadline)

    assert command[-2] == "--deadline"
    assert float(command[-1]) == pytest.approx(deadline, abs=1e-6)


def test_litellm_command_has_no_cooperative_deadline(tmp_path):
    backend = LiteLLMOneShotBackend()

    command = runner._build_backend_command(backend, str(tmp_path), str(tmp_path / "results"), None)

    assert command[-2:] == ["--deadline", "0"]


def test_local_runner_launches_copilot_with_absolute_deadline(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path, timeout=40_000)
    item.backend = CopilotOneShotBackend()
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
    runner._run_backend_local(
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

    match = re.search(r"--deadline ([0-9.]+)", captured["command"][2])
    assert match is not None
    assert float(match.group(1)) > time.time() + 39_000
    assert captured["communicate"]["input"] == "prompt"
    assert result["agent_exit"] == 0


def test_container_runner_launches_copilot_with_absolute_deadline(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path, timeout=40_000)
    item.backend = CopilotOneShotBackend()
    agent_dir = tmp_path / "agent"
    agent_dir.mkdir()
    captured = {}

    class FakeContainerRunner:
        def run(self, config, command, stdin_data):
            captured["command"] = command
            captured["stdin_data"] = stdin_data
            true_bin = shutil.which("true")
            assert true_bin is not None
            proc = subprocess.Popen(
                [true_bin],
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
    runner._run_backend_container(
        item,
        item.backend,
        str(tmp_path),
        str(agent_dir),
        str(agent_dir / "output.jsonl"),
        "prompt",
        result,
    )

    assert captured["command"][-2] == "--deadline"
    assert float(captured["command"][-1]) > time.time() + 39_000
    assert captured["stdin_data"] == "prompt"
    assert result["agent_exit"] == 0


def test_agentic_command_is_unchanged_by_timeout_forwarding():
    class Backend(AgenticBackend):
        def build_command(self, workspace, result_dir):
            return ["agent", workspace, result_dir]

        def parse_output(self, jsonl_path):
            return "", 0, 0

    command = runner._build_backend_command(Backend(), "/workspace", "/results", None)

    assert command == ["agent", "/workspace", "/results"]


def test_copilot_timeout_drains_audit_before_outer_hard_kill(tmp_path, monkeypatch):
    driver = tmp_path / "cooperative_timeout.py"
    driver.write_text(
        """\
import argparse
import json
import time

parser = argparse.ArgumentParser()
parser.add_argument("--deadline", type=float, required=True)
args = parser.parse_args()
while time.time() < args.deadline:
    time.sleep(0.005)
events = [
    {"type": "usage", "input_tokens": 17, "output_tokens": 9, "model_requests": 1},
    {
        "type": "request_audit",
        "provider": "copilot",
        "model_requests": 1,
        "audit_scope": "wire",
        "contract_ok": True,
        "inference_requests": 1,
        "inference_attempts": 1,
        "blocked_requests": 0,
        "system_removed": True,
        "tools_removed": True,
    },
    {"type": "error", "message": "Copilot request reached benchmark deadline"},
    {"type": "result", "status": "timeout", "model_requests": 1},
]
for event in events:
    print(json.dumps(event), flush=True)
# Simulate slow SDK/session cleanup after terminal evidence is already durable.
time.sleep(0.15)
raise SystemExit(1)
"""
    )

    class CooperativeCopilot(CopilotOneShotBackend):
        def build_command(self, workspace, result_dir):
            return [sys.executable, str(driver)]

    item, result_dir = _make_item(tmp_path, timeout=0.2)
    item.backend = CooperativeCopilot()
    monkeypatch.setattr(
        item.backend,
        "materialize_solution",
        lambda *args: pytest.fail("timeout must not materialize"),
    )
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("timeout must not grade"))

    result = runner.run_single_benchmark(item)
    events = [json.loads(line) for line in (result_dir / "agent" / "output.jsonl").read_text().splitlines()]

    assert [event["type"] for event in events] == ["usage", "request_audit", "error", "result"]
    assert result["termination_reason"] == "TIMEOUT"
    assert result["check_verdict"] == "TIMEOUT"
    assert result["model_requests"] == 1
    assert (result["input_tokens"], result["output_tokens"]) == (17, 9)
    assert result["time_secs"] == pytest.approx(0.2, abs=0.02)


def test_copilot_deadline_before_request_with_output_limit_is_not_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.backend = CopilotOneShotBackend()
    item.backend.set_max_output_tokens(64_000)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        audit = StrictCopilotRequestHandler(prompt, max_output_tokens=64_000).audit()
        events = [
            {"type": "request_audit", **audit},
            {"type": "error", "message": "benchmark deadline reached during startup"},
            {"type": "result", "status": "timeout", "model_requests": 0},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("timeout must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("timeout must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "TIMEOUT"
    assert result["check_verdict"] == "TIMEOUT"
    assert result["model_requests"] == 0
    assert result["requested_max_output_tokens"] == 64_000


def test_zero_request_provider_error_preserves_root_cause(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        events = [
            {
                "type": "request_audit",
                "provider": "litellm",
                "model_requests": 0,
                "request_attempts": 0,
                "blocked_requests": 0,
                "system_prompt_present": False,
                "tools_present": False,
                "retries_enabled": False,
                "audit_scope": "adapter",
                "contract_ok": True,
                "wire_audited": False,
                "litellm_completion_invocations": 0,
                "litellm_retries_disabled": True,
                "system_supplied": False,
                "tools_supplied": False,
            },
            {"type": "error", "message": "HTTP 401 Unauthorized"},
            {"type": "result", "status": "error", "model_requests": 0, "retryable": False},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("provider error must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("permanent error must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["error"] == "HTTP 401 Unauthorized"
    assert json.loads((result_dir / "result.json").read_text())["error"] == "HTTP 401 Unauthorized"


def test_post_request_contract_error_preserves_root_cause(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        events = [
            {"type": "usage", "input_tokens": 11, "output_tokens": 0, "model_requests": 1},
            {
                "type": "request_audit",
                "provider": "litellm",
                "model_requests": 1,
                "blocked_requests": 1,
                "audit_scope": "adapter",
                "contract_ok": False,
            },
            {"type": "error", "message": "strict one-shot: blocked second request"},
            {"type": "result", "status": "error", "model_requests": 1, "retryable": False},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("contract error must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("contract error must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["error"] == "strict one-shot: blocked second request"
    assert (result["input_tokens"], result["output_tokens"]) == (11, 0)


def test_invalid_model_zero_output_is_not_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        events = [
            {"type": "usage", "input_tokens": 12, "output_tokens": 0, "model_requests": 1},
            {
                "type": "request_audit",
                "provider": "litellm",
                "model_requests": 1,
                "request_attempts": 1,
                "blocked_requests": 0,
                "system_prompt_present": False,
                "tools_present": False,
                "retries_enabled": False,
                "audit_scope": "adapter",
                "contract_ok": True,
                "wire_audited": False,
                "litellm_completion_invocations": 1,
                "litellm_retries_disabled": True,
                "system_supplied": False,
                "tools_supplied": False,
            },
            {"type": "error", "message": "invalid model"},
            {"type": "result", "status": "error", "model_requests": 1, "retryable": False},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("provider error must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("invalid model must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["error"] == "invalid model"
    assert result["usage"]["model_requests"] == 1
    assert (result["input_tokens"], result["output_tokens"]) == (12, 0)
    assert "infra_retries" not in result


def test_nonempty_response_without_terminal_events_is_not_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    workspaces = []

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        workspaces.append(workspace)
        Path(agent_jsonl).write_text(json.dumps({"type": "response", "text": MODULE}) + "\n")
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("truncated response must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("completed response must not retry"))

    result = runner.run_single_benchmark(item)

    assert len(workspaces) == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["model_requests"] == 1
    assert result["usage"]["model_requests"] == 1
    assert result["usage"]["status"] == "lower_bound"
    assert result["usage"]["input_tokens"] is None
    assert result["usage"]["output_tokens"] is None
    assert "infra_retries" not in result


def test_whitespace_response_is_model_output_and_is_not_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        Path(agent_jsonl).write_text(json.dumps({"type": "response", "text": "\n"}) + "\n")
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("invalid response must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("model output must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["model_requests"] == 1
    assert result["usage"]["model_requests"] == 1
    assert "infra_retries" not in result


def test_partial_model_output_marker_without_terminal_events_is_not_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        Path(agent_jsonl).write_text(
            json.dumps(
                {
                    "type": "model_output_observed",
                    "kind": "assistant.message_delta",
                    "model_requests": 1,
                }
            )
            + "\n"
        )
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("partial output must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("partial output must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["model_requests"] == 1
    assert result["usage"]["model_requests"] == 1
    assert result["usage"]["status"] == "lower_bound"
    assert "infra_retries" not in result


def test_response_evidence_overrides_zero_request_terminal(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        events = [
            {"type": "response", "text": MODULE},
            {
                "type": "request_audit",
                "provider": "litellm",
                "model_requests": 0,
                "request_attempts": 0,
                "blocked_requests": 0,
                "system_prompt_present": False,
                "tools_present": False,
                "retries_enabled": False,
                "audit_scope": "adapter",
                "contract_ok": True,
                "wire_audited": False,
                "litellm_completion_invocations": 0,
                "litellm_retries_disabled": True,
                "system_supplied": False,
                "tools_supplied": False,
            },
            {"type": "error", "message": "usage serialization failed"},
            {"type": "result", "status": "error", "model_requests": 0, "retryable": False},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("truncated response must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("completed response must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["model_requests"] == 1
    assert result["usage"]["model_requests"] == 1
    assert result["usage"]["status"] == "lower_bound"
    assert "infra_retries" not in result


def test_truncated_response_event_is_not_treated_as_empty_startup(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        Path(agent_jsonl).write_text(
            json.dumps({"type": "model_output_observed", "kind": "response", "model_requests": 1})
            + "\n"
            + '{"type":"response","text":"partial'
        )
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("truncated response must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("truncated response must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["model_requests"] == 1
    assert result["usage"]["model_requests"] == 1
    assert result["usage"]["status"] == "lower_bound"
    assert "infra_retries" not in result


def test_copilot_oneshot_retries_zero_output_infra_then_succeeds(tmp_path, monkeypatch):
    item, result_dir = _make_item(tmp_path)
    item.backend = CopilotOneShotBackend()
    item.backend.set_max_output_tokens(64_000)
    item.infra_retries = 1
    workspaces = []
    grader_calls = []

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        workspaces.append(workspace)
        if len(workspaces) == 1:
            events = [
                {"type": "usage", "input_tokens": 0, "output_tokens": 0, "model_requests": 1},
                {
                    "type": "request_audit",
                    "provider": "copilot",
                    "model_requests": 1,
                    "request_attempts": 6,
                    "blocked_requests": 5,
                    "system_prompt_present": False,
                    "tools_present": False,
                    "retries_enabled": False,
                    "audit_scope": "wire",
                    "contract_ok": False,
                    "wire_audited": True,
                    "inference_requests": 1,
                    "inference_attempts": 6,
                    "unknown_requests": 0,
                    "system_removed": True,
                    "tools_removed": True,
                    "requested_max_output_tokens": 64_000,
                    "runtime_max_output_tokens": 32_000,
                    "wire_max_output_tokens": 64_000,
                },
                {"type": "error", "message": "HTTP 503 Service Unavailable"},
                {"type": "result", "status": "error", "model_requests": 1, "retryable": True},
            ]
            result["agent_exit"] = 1
        else:
            events = [
                {"type": "response", "text": MODULE},
                {"type": "usage", "input_tokens": 10, "output_tokens": 5, "model_requests": 1},
                {
                    "type": "request_audit",
                    "provider": "copilot",
                    "model_requests": 1,
                    "request_attempts": 1,
                    "blocked_requests": 0,
                    "system_prompt_present": False,
                    "tools_present": False,
                    "retries_enabled": False,
                    "audit_scope": "wire",
                    "contract_ok": True,
                    "wire_audited": True,
                    "inference_requests": 1,
                    "inference_attempts": 1,
                    "unknown_requests": 0,
                    "system_removed": True,
                    "tools_removed": True,
                    "requested_max_output_tokens": 64_000,
                    "runtime_max_output_tokens": 32_000,
                    "wire_max_output_tokens": 64_000,
                },
                {"type": "result", "status": "success", "model_requests": 1},
            ]
            result["agent_exit"] = 0
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))

    def fake_grader(*_args, **_kwargs):
        grader_calls.append(True)
        _args[5]["check_verdict"] = "PASS"

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)
    monkeypatch.setattr(runner.time, "sleep", lambda _seconds: None)

    result = runner.run_single_benchmark(item)

    assert len(workspaces) == 2
    assert workspaces[0] != workspaces[1]
    assert grader_calls == [True]
    assert result["check_verdict"] == "PASS"
    assert result["termination_reason"] == "OK"
    assert result["infra_retries"] == 1
    assert result["infra_retry_reasons"] == ["no stderr"]
    assert result["requested_max_output_tokens"] == 64_000
    assert result["runtime_max_output_tokens"] == 32_000
    assert result["wire_max_output_tokens"] == 64_000
    attempt_events = result_dir / "agent" / "attempts" / "attempt-0" / "output.jsonl"
    assert "HTTP 503 Service Unavailable" in attempt_events.read_text()


def test_copilot_retry_result_does_not_keep_prior_attempt_wire_metadata(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.backend = CopilotOneShotBackend()
    item.backend.set_max_output_tokens(64_000)
    item.infra_retries = 1
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            events = [
                {"type": "usage", "input_tokens": 10, "output_tokens": 0, "model_requests": 1},
                {
                    "type": "request_audit",
                    "provider": "copilot",
                    "model_requests": 1,
                    "request_attempts": 2,
                    "blocked_requests": 1,
                    "system_prompt_present": False,
                    "tools_present": False,
                    "retries_enabled": False,
                    "audit_scope": "wire",
                    "contract_ok": False,
                    "wire_audited": True,
                    "inference_requests": 1,
                    "inference_attempts": 2,
                    "unknown_requests": 0,
                    "system_removed": True,
                    "tools_removed": True,
                    "requested_max_output_tokens": 64_000,
                    "runtime_max_output_tokens": 32_000,
                    "wire_max_output_tokens": 64_000,
                    "request_sha256": "prior-attempt",
                    "finish_reason": "error",
                },
                {"type": "error", "message": "HTTP 503 Service Unavailable"},
                {"type": "result", "status": "error", "model_requests": 1, "retryable": True},
            ]
            Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
            result["agent_exit"] = 1
            return

        Path(agent_jsonl).write_text("")
        result["agent_exit"] = 1
        result["error"] = "Copilot client failed during startup"

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("infra failure must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _seconds: None)

    result = runner.run_single_benchmark(item)

    assert attempts == 2
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["error"] == "Copilot client failed during startup"
    assert result["model_requests"] == 0
    assert result["provider"] == "copilot"
    assert result["one_shot"] is True
    assert result["requested_max_output_tokens"] == 64_000
    for stale_key in (
        "status",
        "audit_scope",
        "contract_ok",
        "request_attempts",
        "blocked_requests",
        "wire_audited",
        "inference_requests",
        "inference_attempts",
        "unknown_requests",
        "system_removed",
        "tools_removed",
        "runtime_max_output_tokens",
        "wire_max_output_tokens",
        "request_sha256",
        "finish_reason",
        "retryable",
    ):
        assert stale_key not in result


def test_copilot_oneshot_does_not_retry_positive_output_length_failure(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.backend = CopilotOneShotBackend()
    item.infra_retries = 3
    calls = []

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        calls.append(workspace)
        events = [
            {"type": "usage", "input_tokens": 4_080, "output_tokens": 32_000, "model_requests": 1},
            {
                "type": "request_audit",
                "provider": "copilot",
                "model_requests": 1,
                "request_attempts": 7,
                "blocked_requests": 6,
                "system_prompt_present": False,
                "tools_present": False,
                "retries_enabled": False,
                "audit_scope": "wire",
                "contract_ok": False,
                "wire_audited": True,
                "inference_requests": 1,
                "inference_attempts": 7,
                "unknown_requests": 0,
                "system_removed": True,
                "tools_removed": True,
                "finish_reason": "length",
            },
            {"type": "error", "message": "strict one-shot: blocked inference request after the first"},
            {"type": "result", "status": "error", "model_requests": 1},
        ]
        Path(agent_jsonl).write_text("".join(json.dumps(event) + "\n" for event in events))
        result["agent_exit"] = 1

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("length failure must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _seconds: pytest.fail("length failure must not retry"))

    result = runner.run_single_benchmark(item)

    assert len(calls) == 1
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["output_tokens"] == 32_000
    assert result["finish_reason"] == "length"
    assert "infra_retries" not in result


def test_clean_empty_oneshot_stream_is_infra_not_capability_fail(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 3
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        Path(agent_jsonl).write_text("")
        result["agent_exit"] = 0

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(
        item.backend,
        "materialize_solution",
        lambda *args: pytest.fail("invalid stream must not materialize"),
    )
    monkeypatch.setattr(runner, "_run_grader_local", lambda *args: pytest.fail("invalid stream must not grade"))
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: pytest.fail("clean empty stream must not retry"))

    result = runner.run_single_benchmark(item)

    assert attempts == 1
    assert result["check_verdict"] == "ERROR"
    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["model_requests"] == 0


def test_nonzero_empty_oneshot_startup_is_retried(tmp_path, monkeypatch):
    item, _result_dir = _make_item(tmp_path)
    item.infra_retries = 1
    attempts = 0

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        nonlocal attempts
        attempts += 1
        assert Path(agent_jsonl).read_text() == ""
        if attempts == 1:
            result["agent_exit"] = -2
            result["error"] = "container startup failed"
            return
        _write_clean_response(agent_jsonl)
        result["agent_exit"] = 0

    def fake_grader(*args):
        args[5]["check_verdict"] = "PASS"

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)
    monkeypatch.setattr(runner.time, "sleep", lambda _delay: None)

    result = runner.run_single_benchmark(item)

    assert attempts == 2
    assert result["termination_reason"] == "OK"
    assert result["check_verdict"] == "PASS"
    assert result["infra_retries"] == 1
