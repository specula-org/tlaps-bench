"""Codex CLI single-turn backend contract."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from evaluator.backends import get_backend, list_backends
from evaluator.backends.codex_single_turn import CodexSingleTurnBackend
from evaluator.backends.codex_usage_wrapper import CODEX_CHILD_USAGE_VERSION

MODULE = "---- MODULE Example ----\nTHEOREM Target == TRUE\nPROOF OBVIOUS\n====\n"


class _Mode:
    def build_one_shot_prompt(self, benchmark_path, dependencies):
        return f"one shot: {benchmark_path}; dependencies={dependencies}"


def _write_events(path: Path, *events: dict[str, object]) -> None:
    path.write_text("".join(json.dumps(event) + "\n" for event in events))


def _zero_tool_audit(thread_id: str = "root") -> dict[str, object]:
    return {
        "type": "tlaps.codex_child_usage",
        "version": CODEX_CHILD_USAGE_VERSION,
        "tool_calls_scope": "session_tree",
        "root_thread_id": thread_id,
        "child_count": 0,
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "requests": [
            {
                "input_tokens": 10,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 5,
                "reasoning_output_tokens": 0,
                "model": "gpt-5.5",
                "provider": "openai",
            }
        ],
        "complete": True,
        "warning_codes": [],
        "tool_calls": {
            "total": 0,
            "tlaps": 0,
            "tlc": 0,
            "apalache": 0,
            "other": 0,
            "available": True,
            "complete": True,
            "is_lower_bound": False,
            "warnings": [],
        },
    }


def _completed_stream(path: Path, *items: dict[str, object]) -> None:
    _write_events(
        path,
        {"type": "tlaps.codex_child_usage.started", "version": CODEX_CHILD_USAGE_VERSION},
        {"type": "thread.started", "thread_id": "root"},
        {"type": "turn.started"},
        *items,
        {"type": "turn.completed", "usage": {"input_tokens": 10, "output_tokens": 5}},
        _zero_tool_audit(),
    )


def test_registry_exposes_codex_single_turn_backend():
    assert "codex_single_turn" in list_backends()
    assert isinstance(get_backend("codex_single_turn", model="gpt-5.6-sol"), CodexSingleTurnBackend)


def test_command_is_read_only_tool_free_single_codex_turn(tmp_path):
    backend = CodexSingleTurnBackend(model="gpt-5.6-sol")
    backend.set_reasoning_effort("medium")

    command = backend.build_command("/workspace", "/results")

    assert command[:5] == ["python3", "/opt/codex_usage_wrapper.py", "--", "codex", "exec"]
    assert command[-1] == "-"
    assert command.count("exec") == 1
    assert command[command.index("--sandbox") + 1] == "read-only"
    assert "--ignore-user-config" in command
    assert "--ignore-rules" in command
    assert "--dangerously-bypass-approvals-and-sandbox" not in command
    assert "--ephemeral" not in command
    assert 'approval_policy="never"' in command
    assert 'web_search="disabled"' in command
    assert "agents.enabled=false" in command
    assert "apps._default.enabled=false" in command
    assert "model_reasoning_effort=medium" in command
    disabled = {command[index + 1] for index, value in enumerate(command[:-1]) if value == "--disable"}
    assert {
        "shell_tool",
        "unified_exec",
        "code_mode",
        "code_mode_host",
        "code_mode_only",
        "code_mode_buffered_exec",
        "multi_agent",
        "multi_agent_v2",
        "apps",
        "browser_use",
        "computer_use",
        "image_generation",
        "view_image",
        "goals",
        "tool_suggest",
    } <= disabled

    native = backend.build_command(str(tmp_path), str(tmp_path / "results"))
    assert native[0] == sys.executable
    assert Path(native[1]).name == "codex_usage_wrapper.py"


def test_backend_uses_one_shot_prompt_and_disables_continuations():
    backend = CodexSingleTurnBackend()

    prompt = backend.build_prompt(_Mode(), "/tmp/Task.tla", ["/tmp/Model.tla"], "Task.tla", "tlapm", "lib")
    metadata = backend.initial_result_metadata()

    assert prompt == (
        "Do not call or suggest any tools. Use only the target and context embedded below, "
        "and return the requested module directly.\n\n"
        "one shot: /tmp/Task.tla; dependencies=['/tmp/Model.tla']"
    )
    assert backend.approach == "single_turn_tool_free"
    assert backend.project_skills_dir is None
    assert backend.capabilities.model_preflight is True
    assert backend.capabilities.max_continuations == 0
    assert metadata["one_shot"] is False
    assert metadata["single_turn"] is True
    assert metadata["model_request_count_visible"] is False
    assert metadata["model_requests"] is None


def test_backend_rejects_bedrock_because_user_provider_config_is_ignored():
    backend = CodexSingleTurnBackend(model="openai.gpt-5.5")

    assert backend.check_auth() == (
        "codex_single_turn: Amazon Bedrock models are unsupported; use an OpenAI Codex model"
    )


def test_protocol_audit_accepts_multiple_messages_with_one_tool_free_turn(tmp_path):
    output = tmp_path / "output.jsonl"
    _completed_stream(
        output,
        {"type": "item.completed", "item": {"id": "progress", "type": "agent_message", "text": "Working"}},
        {"type": "item.completed", "item": {"id": "final", "type": "agent_message", "text": MODULE}},
    )
    (tmp_path / "codex_last_message.txt").write_text(MODULE)

    metadata = CodexSingleTurnBackend().parse_run_metadata(str(output))

    assert metadata["protocol_counts"] == {
        "thread_started": 1,
        "turn_started": 1,
        "turn_completed": 1,
        "turn_failed": 0,
        "agent_messages": 2,
        "reasoning_items": 0,
        "tool_items": 0,
        "non_tool_items": 0,
    }
    assert metadata["tool_calls"]["total"] == 0
    assert metadata["tool_calls"]["complete"] is True
    assert metadata["single_turn_observed"] is True
    assert metadata["tool_free_observed"] is True
    assert metadata["single_turn_tool_free_observed"] is True
    assert metadata["model_request_count_visible"] is True
    assert metadata["model_request_count_source"] == "codex_rollout_token_count"
    assert metadata["model_requests"] == 1
    assert metadata["one_model_request_observed"] is True
    assert metadata["one_shot_approximation_observed"] is True


def test_protocol_audit_rejects_observed_tool_item(tmp_path):
    output = tmp_path / "output.jsonl"
    _completed_stream(
        output,
        {
            "type": "item.completed",
            "item": {"id": "command", "type": "command_execution", "command": "pwd"},
        },
        {"type": "item.completed", "item": {"id": "final", "type": "agent_message", "text": MODULE}},
    )
    (tmp_path / "codex_last_message.txt").write_text(MODULE)

    metadata = CodexSingleTurnBackend().parse_run_metadata(str(output))

    assert metadata["protocol_counts"]["tool_items"] == 1
    assert metadata["observed_tool_item_types"] == ["command_execution"]
    assert metadata["tool_free_observed"] is False
    assert metadata["single_turn_tool_free_observed"] is False


def test_code_mode_disabled_notice_is_not_a_tool_dispatch(tmp_path):
    output = tmp_path / "output.jsonl"
    _completed_stream(
        output,
        {
            "type": "item.completed",
            "item": {
                "id": "notice",
                "type": "error",
                "message": "Code Mode is unavailable because code-mode host is disabled.",
            },
        },
        {"type": "item.completed", "item": {"id": "final", "type": "agent_message", "text": MODULE}},
    )
    (tmp_path / "codex_last_message.txt").write_text(MODULE)

    metadata = CodexSingleTurnBackend().parse_run_metadata(str(output))

    assert metadata["protocol_counts"]["non_tool_items"] == 1
    assert metadata["protocol_counts"]["tool_items"] == 0
    assert metadata["tool_free_observed"] is True
    assert metadata["one_shot_approximation_observed"] is True


def test_materialize_solution_uses_only_codex_final_message(tmp_path):
    output = tmp_path / "output.jsonl"
    output.write_text('{"type":"turn.completed","usage":{"input_tokens":1,"output_tokens":1}}\n')
    (tmp_path / "codex_last_message.txt").write_text(f"```tla\n{MODULE}```\n")
    destination = tmp_path / "Example.tla"
    destination.write_text("unchanged")

    assert CodexSingleTurnBackend().materialize_solution(str(output), str(destination)) is True
    assert destination.read_text() == MODULE
