"""Tool-free, single-turn Codex CLI approximation of a one-shot request."""

from __future__ import annotations

import json
import os
import sys
import tempfile
from contextlib import suppress
from pathlib import Path
from typing import Any

from evaluator.termination import TerminationReason

from .base import BackendCapabilities, SubmissionDisposition, SubmissionPlan
from .codex import CodexBackend
from .oneshot import _reconstruct_marked_solution, _unwrap_tla_fence


class CodexSingleTurnBackend(CodexBackend):
    """Run one tool-free Codex turn and grade its final message as a module.

    This is deliberately not the strict ``OneShotBackend`` contract.  Codex
    exposes one logical turn and aggregate token usage, but not the number of
    underlying model requests used to produce that turn.
    """

    name = "codex_single_turn"
    approach = "single_turn_tool_free"
    project_skills_dir = None
    capabilities = BackendCapabilities(
        model_preflight=True,
        default_infra_retries=3,
        max_infra_retries=None,
        max_continuations=0,
    )

    def _uses_bedrock(self) -> bool:
        # User config is intentionally ignored for protocol isolation. Bedrock
        # needs provider configuration from that file, so this backend supports
        # only Codex's OpenAI/ChatGPT/Azure authentication paths.
        return False

    def check_auth(self) -> str | None:
        if self.model.startswith("openai."):
            return "codex_single_turn: Amazon Bedrock models are unsupported; use an OpenAI Codex model"
        return super().check_auth()

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        last_message = os.path.join(result_dir, "codex_last_message.txt")
        wrapper = (
            ["python3", "/opt/codex_usage_wrapper.py"]
            if workspace == "/workspace"
            else [sys.executable, os.path.join(os.path.dirname(__file__), "codex_usage_wrapper.py")]
        )
        command = [
            *wrapper,
            "--",
            "codex",
            "exec",
            "--ignore-user-config",
            "--ignore-rules",
            "--sandbox",
            "read-only",
            "-C",
            workspace,
            "-m",
            self.model,
            "-c",
            'approval_policy="never"',
            "-c",
            'web_search="disabled"',
            "-c",
            "agents.enabled=false",
            "-c",
            "apps._default.enabled=false",
            "--disable",
            "shell_tool",
            "--disable",
            "unified_exec",
            "--disable",
            "code_mode",
            "--disable",
            "code_mode_host",
            "--disable",
            "code_mode_only",
            "--disable",
            "code_mode_buffered_exec",
            "--disable",
            "multi_agent",
            "--disable",
            "multi_agent_v2",
            "--disable",
            "apps",
            "--disable",
            "browser_use",
            "--disable",
            "computer_use",
            "--disable",
            "image_generation",
            "--disable",
            "view_image",
            "--disable",
            "goals",
            "--disable",
            "tool_suggest",
            "--json",
            "-o",
            last_message,
            "-",
        ]
        if self.reasoning_effort is not None:
            command[-1:-1] = ["-c", f"model_reasoning_effort={self.reasoning_effort}"]
        return command

    def build_prompt(
        self,
        mode: Any,
        benchmark_path: str,
        dependencies: list[str],
        benchmark_basename: str,
        tlapm_path: str,
        tlapm_lib: str,
    ) -> str:
        del benchmark_basename, tlapm_path, tlapm_lib
        prompt = mode.build_one_shot_prompt(benchmark_path, dependencies)
        return (
            "Do not call or suggest any tools. Use only the target and context embedded below, "
            "and return the requested module directly.\n\n"
            f"{prompt}"
        )

    @staticmethod
    def public_pricing_configuration_error() -> str | None:
        # ``--ignore-user-config`` prevents a host service_tier from changing
        # this execution, so it must not block public-price accounting.
        return None

    def initial_result_metadata(self) -> dict[str, object]:
        return {
            **super().initial_result_metadata(),
            "one_shot": False,
            "single_turn": True,
            "tool_free_requested": True,
            "model_request_count_visible": False,
            "model_requests": None,
        }

    def prepare_submission(
        self,
        jsonl_path: str,
        destination: str,
        termination_reason: str,
        error: str,
        *,
        allow_materialization: bool,
    ) -> SubmissionPlan:
        if not allow_materialization:
            return SubmissionPlan(copy_solution=False)
        if termination_reason == TerminationReason.INFRA_ERROR:
            return SubmissionPlan(
                disposition=SubmissionDisposition.ERROR,
                copy_solution=False,
                error=error or "Codex single-turn execution failed",
            )
        if termination_reason == TerminationReason.TIMEOUT:
            return SubmissionPlan(
                disposition=SubmissionDisposition.TIMEOUT,
                copy_solution=False,
                error=error or None,
            )
        if termination_reason != TerminationReason.OK:
            return SubmissionPlan(
                disposition=SubmissionDisposition.ERROR,
                copy_solution=False,
                error=error or f"Codex single-turn run ended with {termination_reason}",
            )

        materialized = self.materialize_solution(jsonl_path, destination)
        metadata: dict[str, object] = {"materialized": materialized}
        if not materialized:
            message = "Codex final message could not be materialized"
            metadata["materialization_error"] = message
            return SubmissionPlan(
                disposition=SubmissionDisposition.FAIL,
                copy_solution=False,
                error=message,
                metadata=metadata,
            )
        return SubmissionPlan(copy_solution=True, metadata=metadata)

    def parse_run_metadata(self, jsonl_path: str) -> dict[str, object]:
        metadata = super().parse_run_metadata(jsonl_path)
        counts = {
            "thread_started": 0,
            "turn_started": 0,
            "turn_completed": 0,
            "turn_failed": 0,
            "agent_messages": 0,
            "reasoning_items": 0,
            "tool_items": 0,
            "non_tool_items": 0,
        }
        thread_ids: set[str] = set()
        tool_item_types: set[str] = set()
        request_audits: list[tuple[bool, int]] = []
        final_message = Path(jsonl_path).with_name("codex_last_message.txt")
        final_message_present = False
        with suppress(OSError, UnicodeError):
            final_message_present = bool(final_message.read_text(encoding="utf-8").strip())

        try:
            with open(jsonl_path, encoding="utf-8", errors="replace") as stream:
                for raw in stream:
                    try:
                        event = json.loads(raw)
                    except json.JSONDecodeError:
                        continue
                    if not isinstance(event, dict):
                        continue
                    event_type = event.get("type")
                    if event_type == "thread.started":
                        counts["thread_started"] += 1
                        thread_id = event.get("thread_id")
                        if isinstance(thread_id, str) and thread_id:
                            thread_ids.add(thread_id)
                    elif event_type == "turn.started":
                        counts["turn_started"] += 1
                    elif event_type == "turn.completed":
                        counts["turn_completed"] += 1
                    elif event_type == "turn.failed":
                        counts["turn_failed"] += 1
                    elif event_type == "tlaps.codex_child_usage":
                        requests = event.get("requests")
                        warning_codes = event.get("warning_codes")
                        request_audits.append(
                            (
                                event.get("complete") is True and isinstance(requests, list) and warning_codes == [],
                                len(requests) if isinstance(requests, list) else 0,
                            )
                        )
                    if event_type != "item.completed":
                        continue
                    item = event.get("item")
                    if not isinstance(item, dict):
                        continue
                    item_type = item.get("type")
                    if item_type == "agent_message":
                        counts["agent_messages"] += 1
                    elif item_type == "reasoning":
                        counts["reasoning_items"] += 1
                    elif item_type in {
                        "command_execution",
                        "file_change",
                        "mcp_tool_call",
                        "collab_tool_call",
                        "todo_list",
                        "web_search",
                    }:
                        counts["tool_items"] += 1
                        tool_item_types.add(item_type)
                    elif isinstance(item_type, str):
                        counts["non_tool_items"] += 1
        except OSError:
            pass

        tool_calls = metadata.get("tool_calls")
        complete_zero_tool_audit = (
            isinstance(tool_calls, dict)
            and tool_calls.get("available") is True
            and tool_calls.get("complete") is True
            and tool_calls.get("total") == 0
        )
        single_turn_observed = (
            counts["thread_started"] == 1
            and len(thread_ids) == 1
            and counts["turn_started"] == 1
            and counts["turn_completed"] == 1
            and counts["turn_failed"] == 0
            and final_message_present
        )
        tool_free_observed = counts["tool_items"] == 0 and complete_zero_tool_audit
        model_request_count_visible = len(request_audits) == 1 and request_audits[0][0]
        model_requests = request_audits[0][1] if model_request_count_visible else None
        metadata.update(
            {
                "one_shot": False,
                "single_turn": True,
                "tool_free_requested": True,
                "model_request_count_visible": model_request_count_visible,
                "model_request_count_source": "codex_rollout_token_count" if model_request_count_visible else None,
                "model_requests": model_requests,
                "protocol_counts": counts,
                "observed_thread_ids": sorted(thread_ids),
                "observed_tool_item_types": sorted(tool_item_types),
                "final_message_present": final_message_present,
                "single_turn_observed": single_turn_observed,
                "tool_free_observed": tool_free_observed,
                "single_turn_tool_free_observed": single_turn_observed and tool_free_observed,
                "one_model_request_observed": model_requests == 1,
                "one_shot_approximation_observed": (
                    single_turn_observed and tool_free_observed and model_requests == 1
                ),
            }
        )
        return metadata

    def materialize_solution(self, jsonl_path: str, destination: str) -> bool:
        last_message = Path(jsonl_path).with_name("codex_last_message.txt")
        try:
            response = last_message.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            return False
        if not response.strip():
            return False

        solution = _unwrap_tla_fence(response)
        target = Path(destination)
        solution = _reconstruct_marked_solution(target, solution)
        if solution is None:
            return False

        temporary: str | None = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                dir=target.parent,
                prefix=f".{target.name}.",
                suffix=".tmp",
                delete=False,
            ) as stream:
                temporary = stream.name
                stream.write(solution)
            os.replace(temporary, target)
        except OSError:
            if temporary is not None:
                with suppress(OSError):
                    os.unlink(temporary)
            return False
        return True
