"""Shared one-shot backend contract and provider wiring."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

from evaluator import runner
from evaluator.backends import get_backend, list_backends
from evaluator.backends.agentic import AgenticBackend
from evaluator.backends.copilot_oneshot import CopilotOneShotBackend
from evaluator.backends.litellm_oneshot import LiteLLMOneShotBackend
from evaluator.backends.oneshot import OneShotBackend

MODULE = "---- MODULE Example ----\nTHEOREM Target == TRUE\nPROOF OBVIOUS\n====\n"


def _write_events(path, *events):
    path.write_text("".join(json.dumps(event) + "\n" for event in events))


class _OneShotMode:
    name = "proof-completion"
    description = "test mode"

    def __init__(self, benchmark_root):
        self._benchmark_root = str(benchmark_root)

    def benchmark_dir(self):
        return self._benchmark_root

    def get_benchmark_files(self, filter_pattern=None):
        return [os.path.join(self._benchmark_root, "Suite", "Example.tla")]

    def get_dependencies(self, benchmark_path):
        return []

    def checker_binary_path(self):
        return "/bin/true"

    def build_one_shot_prompt(self, benchmark_path, dependencies):
        return "return one complete module"


def test_registry_exposes_both_oneshot_providers():
    assert "litellm_oneshot" in list_backends()
    assert "copilot_oneshot" in list_backends()
    assert isinstance(get_backend("litellm_oneshot", model="openai/gpt-5"), LiteLLMOneShotBackend)
    assert isinstance(get_backend("copilot_oneshot", model="gpt-5"), CopilotOneShotBackend)


def test_shared_command_and_capabilities(tmp_path):
    backend = LiteLLMOneShotBackend(model="anthropic/claude-sonnet-4-6")

    assert backend.build_command("/workspace", "/results") == [
        "python3",
        "/opt/oneshot_runner.py",
        "--provider",
        "litellm",
        "--workspace",
        "/workspace",
        "--result-dir",
        "/results",
        "--model",
        "anthropic/claude-sonnet-4-6",
    ]
    assert isinstance(backend, OneShotBackend)
    assert not isinstance(backend, AgenticBackend)
    assert backend.approach == "one_shot"
    assert backend.capabilities.model_preflight is False
    assert backend.capabilities.max_continuations == 0
    assert backend.capabilities.default_infra_retries == 0


def test_shared_command_uses_module_runner_for_native_execution(tmp_path):
    backend = CopilotOneShotBackend(model="gpt-5")

    command = backend.build_command(str(tmp_path), str(tmp_path / "results"))

    assert command[:3] == [sys.executable, "-m", "evaluator.backends.oneshot_runner"]
    assert command[3:6] == ["--provider", "copilot", "--workspace"]


def test_parse_output_and_request_metadata(tmp_path):
    events = tmp_path / "output.jsonl"
    events.write_text(
        "not json\n"
        + json.dumps({"type": "response", "text": MODULE})
        + "\n"
        + json.dumps({"type": "usage", "input_tokens": 120, "output_tokens": 80})
        + "\n"
        + json.dumps(
            {
                "type": "request_audit",
                "provider": "copilot",
                "model_requests": 1,
                "audit_scope": "wire",
                "contract_ok": True,
                "inference_requests": 1,
                "request_sha256": "abc123",
                "system_removed": True,
                "tools_removed": True,
            }
        )
        + "\n"
    )
    backend = CopilotOneShotBackend(model="gpt-5")

    transcript, input_tokens, output_tokens = backend.parse_output(str(events))
    metadata = backend.parse_run_metadata(str(events))

    assert transcript == f"[AGENT] {MODULE}\n"
    assert (input_tokens, output_tokens) == (120, 80)
    assert metadata == {
        "one_shot": True,
        "provider": "copilot",
        "audit_scope": "wire",
        "contract_ok": True,
        "request_sha256": "abc123",
        "system_removed": True,
        "tools_removed": True,
        "model_requests": 1,
    }


def test_materializes_raw_response_verbatim_atomically(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    destination.write_text("original\n")
    response = f"\n{MODULE}\n"
    _write_events(events, {"type": "response", "text": response})

    assert LiteLLMOneShotBackend().materialize_solution(str(events), str(destination)) is True
    assert destination.read_text() == response


def test_materializes_module_with_leading_comments_verbatim(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    response = "\\* Contributor: Example Author\n\\* Source: Example Paper\n\n" + MODULE
    _write_events(events, {"type": "response", "text": response})

    assert LiteLLMOneShotBackend().materialize_solution(str(events), str(destination)) is True
    assert destination.read_text() == response


def test_materializes_unique_tla_fence(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    _write_events(events, {"type": "response", "text": f"```tla\n{MODULE}```"})

    assert CopilotOneShotBackend().materialize_solution(str(events), str(destination)) is True
    assert destination.read_text() == MODULE


def test_materializes_non_tla_structures_verbatim_for_grader_validation(tmp_path):
    backend = LiteLLMOneShotBackend()
    destination = tmp_path / "Example.tla"
    destination.write_text("original\n")
    responses = [
        "PROOF OBVIOUS",
        f"@@ -1,2 +1,2 @@\n+{MODULE}",
        f"```tla\n{MODULE}```\n```tla\n{MODULE}```",
        f"```text\n{MODULE}```",
        f"Here is the module:\n```tla\n{MODULE}```",
        f"{MODULE}\nignored after the module",
    ]

    for index, response in enumerate(responses):
        events = tmp_path / f"output-{index}.jsonl"
        _write_events(events, {"type": "response", "text": response})
        assert backend.materialize_solution(str(events), str(destination)) is True
        assert destination.read_text() == response


def test_materialize_rejects_ambiguous_response_events(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    _write_events(events, {"type": "response", "text": MODULE}, {"type": "response", "text": MODULE})

    assert LiteLLMOneShotBackend().materialize_solution(str(events), str(destination)) is False
    assert not destination.exists()


def test_materialize_rejects_extra_empty_response_event(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    response = "PROOF OBVIOUS"
    _write_events(
        events,
        {"type": "response", "text": "\n  "},
        {"type": "response", "text": response},
    )

    assert LiteLLMOneShotBackend().materialize_solution(str(events), str(destination)) is False
    assert not destination.exists()


def test_materialize_rejects_valid_module_mixed_with_another_response(tmp_path):
    events = tmp_path / "output.jsonl"
    destination = tmp_path / "Example.tla"
    _write_events(events, {"type": "response", "text": "preface"}, {"type": "response", "text": MODULE})

    assert LiteLLMOneShotBackend().materialize_solution(str(events), str(destination)) is False
    assert not destination.exists()


def test_copilot_oneshot_requires_explicit_token_and_has_no_session(monkeypatch):
    for key in CopilotOneShotBackend.env_keys:
        monkeypatch.delenv(key, raising=False)
    backend = CopilotOneShotBackend()

    assert backend.check_auth() == "copilot_oneshot: COPILOT_GITHUB_TOKEN, GH_TOKEN, or GITHUB_TOKEN not set"
    assert backend.session_state_dir is None
    assert backend.install_script == "install-copilot-sdk.sh"
    assert "api.github.com" in backend.firewall_hosts()

    monkeypatch.setenv("GITHUB_TOKEN", "test-token")
    assert backend.check_auth() is None


def test_litellm_oneshot_reuses_litellm_auth_and_firewall(monkeypatch):
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    backend = LiteLLMOneShotBackend(model="anthropic/claude-sonnet-4-6")

    assert backend.check_auth() == "litellm_oneshot: ANTHROPIC_API_KEY not set for anthropic model"
    assert backend.install_script == "install-litellm-oneshot.sh"
    assert "api.anthropic.com" in backend.firewall_hosts()

    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    assert backend.check_auth() is None


def test_unstructured_response_is_materialized_and_left_to_grader(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    benchmark = benchmark_root / "Suite" / "Example.tla"
    benchmark.parent.mkdir(parents=True)
    benchmark.write_text(MODULE)
    output_dir = tmp_path / "results"
    backend = LiteLLMOneShotBackend()
    mode = _OneShotMode(benchmark_root)
    item = runner.WorkItem(
        benchmark_path=str(benchmark),
        output_dir=str(output_dir),
        timeout=10,
        check_timeout=10,
        backend=backend,
        mode=mode,  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        infra_retries=0,
    )
    grader_calls = []

    def fake_agent(
        item_, backend_, mode_, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        with open(agent_jsonl, "w") as stream:
            stream.write(json.dumps({"type": "response", "text": "PROOF OBVIOUS"}) + "\n")
            stream.write(
                json.dumps({"type": "usage", "input_tokens": 10, "output_tokens": 3, "model_requests": 1}) + "\n"
            )
            stream.write(
                json.dumps(
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
                    }
                )
                + "\n"
            )
            stream.write(json.dumps({"type": "result", "status": "success", "model_requests": 1}) + "\n")
        result["agent_exit"] = 0

    def fake_grader(item_, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        grader_calls.append(workspace)
        result["check_verdict"] = "PASS"

    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)

    result = runner.run_single_benchmark(item)
    solution = output_dir / "Suite" / "Example" / "agent" / "solution.tla"

    assert result["termination_reason"] == "OK"
    assert result["check_verdict"] == "PASS"
    assert result["materialized"] is True
    assert result["model_requests"] == 1
    assert len(grader_calls) == 1
    assert solution.read_text() == "PROOF OBVIOUS"


def test_second_request_violation_is_error_even_after_model_output(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    benchmark = benchmark_root / "Suite" / "Example.tla"
    benchmark.parent.mkdir(parents=True)
    benchmark.write_text(MODULE)
    output_dir = tmp_path / "results"
    backend = LiteLLMOneShotBackend()
    item = runner.WorkItem(
        benchmark_path=str(benchmark),
        output_dir=str(output_dir),
        timeout=10,
        check_timeout=10,
        backend=backend,
        mode=_OneShotMode(benchmark_root),  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        infra_retries=0,
    )
    materialize_calls = []
    grader_calls = []

    def fake_agent(
        item_, backend_, mode_, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        with open(agent_jsonl, "w") as stream:
            stream.write(json.dumps({"type": "response", "text": MODULE}) + "\n")
            stream.write(
                json.dumps({"type": "usage", "input_tokens": 40, "output_tokens": 20, "model_requests": 1}) + "\n"
            )
            stream.write(
                json.dumps(
                    {
                        "type": "request_audit",
                        "provider": "copilot",
                        "model_requests": 1,
                        "audit_scope": "wire",
                        "contract_ok": False,
                        "inference_requests": 1,
                        "inference_attempts": 2,
                        "blocked_requests": 1,
                    }
                )
                + "\n"
            )
            stream.write(json.dumps({"type": "result", "status": "error", "model_requests": 2}) + "\n")
        result["agent_exit"] = 1

    def fake_materialize(jsonl_path, destination):
        materialize_calls.append((jsonl_path, destination))
        return True

    def fake_grader(item_, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        grader_calls.append(workspace)
        result["check_verdict"] = "PASS"

    monkeypatch.setattr(runner, "_run_backend_local", fake_agent)
    monkeypatch.setattr(backend, "materialize_solution", fake_materialize)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)

    result = runner.run_single_benchmark(item)
    solution = output_dir / "Suite" / "Example" / "agent" / "solution.tla"

    assert result["termination_reason"] == "INFRA_ERROR"
    assert result["check_verdict"] == "ERROR"
    assert result["error"] == "one-shot request contract violation"
    assert result["model_requests"] == 2
    assert result["output_tokens"] == 20
    assert "materialized" not in result
    assert materialize_calls == []
    assert grader_calls == []
    assert not solution.exists()


def _install_cli_fakes(monkeypatch, tmp_path, preflight_calls, captured_items):
    benchmark_root = tmp_path / "benchmark"
    mode = _OneShotMode(benchmark_root)
    monkeypatch.setattr(runner, "get_mode", lambda *args: mode)
    monkeypatch.setattr(runner, "ensure_image", lambda force=False: None)
    monkeypatch.setattr(runner, "_run_preflight", lambda backend: preflight_calls.append(backend.name))
    monkeypatch.setattr(runner, "update_summary", lambda *args: None)

    def fake_run(item):
        captured_items.append(item)
        return {
            "benchmark": "Suite/Example.tla",
            "check_verdict": "FAIL",
            "time_secs": 0,
            "input_tokens": 1,
            "output_tokens": 1,
        }

    monkeypatch.setattr(runner, "run_single_benchmark", fake_run)


def test_cli_uses_zero_infra_retries_and_skips_model_preflight_for_oneshot(tmp_path, monkeypatch):
    preflight_calls = []
    captured_items = []
    _install_cli_fakes(monkeypatch, tmp_path, preflight_calls, captured_items)
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "tlaps-bench",
            "--backend",
            "litellm_oneshot",
            "--output-dir",
            str(tmp_path / "results"),
        ],
    )

    runner.main()

    assert len(captured_items) == 1
    assert captured_items[0].infra_retries == 0
    assert preflight_calls == []


@pytest.mark.parametrize(
    "extra_args, expected_error",
    [
        (["--infra-retries", "1"], "strict one-shot backends require --infra-retries 0"),
        (["--max-continuations", "1"], "does not support --max-continuations"),
    ],
)
def test_cli_rejects_non_oneshot_controls(tmp_path, monkeypatch, capsys, extra_args, expected_error):
    preflight_calls = []
    captured_items = []
    _install_cli_fakes(monkeypatch, tmp_path, preflight_calls, captured_items)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "tlaps-bench",
            "--backend",
            "litellm_oneshot",
            "--output-dir",
            str(tmp_path / "results"),
            *extra_args,
        ],
    )

    with pytest.raises(SystemExit) as exc_info:
        runner.main()

    assert exc_info.value.code == 2
    assert expected_error in capsys.readouterr().err
    assert preflight_calls == []
    assert captured_items == []


@pytest.mark.parametrize(
    ("infra_retries", "max_continuations", "expected_error"),
    [
        (0.0, 0, "--infra-retries must be an integer"),
        (False, 0, "--infra-retries must be an integer"),
        (-1, 0, "--infra-retries must be >= 0"),
        (1, 0, "strict one-shot backends require --infra-retries 0"),
        (0, 0.0, "--max-continuations must be an integer"),
        (0, False, "--max-continuations must be an integer"),
        (0, 1, "does not support --max-continuations"),
    ],
)
def test_direct_work_item_rejects_unsupported_controls_before_side_effects(
    tmp_path,
    monkeypatch,
    infra_retries,
    max_continuations,
    expected_error,
):
    benchmark_root = tmp_path / "benchmark"
    benchmark = benchmark_root / "Suite" / "Example.tla"
    benchmark.parent.mkdir(parents=True)
    benchmark.write_text(MODULE)
    output_dir = tmp_path / "results"
    result_dir = output_dir / "Suite" / "Example"
    result_dir.mkdir(parents=True)
    existing = result_dir / "result.json"
    existing.write_text('{"keep": true}')
    item = runner.WorkItem(
        benchmark_path=str(benchmark),
        output_dir=str(output_dir),
        timeout=10,
        check_timeout=10,
        backend=LiteLLMOneShotBackend(),
        mode=_OneShotMode(benchmark_root),  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
        infra_retries=infra_retries,
        max_continuations=max_continuations,
    )
    monkeypatch.setattr(runner.quota, "wait_for_quota", lambda *args: pytest.fail("quota must not run"))

    with pytest.raises(ValueError, match=expected_error):
        runner.run_single_benchmark(item)

    assert existing.read_text() == '{"keep": true}'


def test_direct_work_item_uses_oneshot_retry_default_and_runs_once(tmp_path, monkeypatch):
    benchmark_root = tmp_path / "benchmark"
    benchmark = benchmark_root / "Suite" / "Example.tla"
    benchmark.parent.mkdir(parents=True)
    benchmark.write_text(MODULE)
    item = runner.WorkItem(
        benchmark_path=str(benchmark),
        output_dir=str(tmp_path / "results"),
        timeout=10,
        check_timeout=10,
        backend=LiteLLMOneShotBackend(),
        mode=_OneShotMode(benchmark_root),  # ty:ignore[invalid-argument-type]
        tlapm_path="/bin/true",
        tlapm_lib="",
    )
    calls = []

    def fake_backend(
        item_, backend, mode, workspace, agent_dir, agent_jsonl, prompt, result, checker_bin, canonical_dir=None
    ):
        calls.append(workspace)
        _write_events(
            Path(agent_jsonl),
            {"type": "response", "text": MODULE},
            {"type": "usage", "input_tokens": 3, "output_tokens": 2, "model_requests": 1},
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
        )
        result["agent_exit"] = 0

    def fake_grader(item_, workspace, basename, grading_dir, check_result_path, result, canonical_dir=None):
        result["check_verdict"] = "FAIL"

    monkeypatch.setattr(runner, "_run_backend_local", fake_backend)
    monkeypatch.setattr(runner, "_run_grader_local", fake_grader)

    runner.run_single_benchmark(item)

    assert item.infra_retries == 0
    assert len(calls) == 1
