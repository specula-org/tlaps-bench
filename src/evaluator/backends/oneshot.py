"""Shared host-side contract for single-request model backends."""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
from collections.abc import Iterator
from contextlib import suppress
from pathlib import Path
from typing import Any

from evaluator.termination import TerminationReason

from .base import (
    Backend,
    BackendCapabilities,
    SubmissionDisposition,
    SubmissionPlan,
)

_FENCED_BLOCK = re.compile(r"```(?P<language>[^\n`]*)\r?\n(?P<body>.*?)```", re.DOTALL)
_REQUEST_COUNT_KEYS = (
    "model_requests",
    "litellm_completion_invocations",
    "inference_requests",
    "request_count",
)


def _as_nonnegative_int(value: object) -> int:
    """Return a safe token/request count for loosely typed JSON events."""
    if isinstance(value, bool):
        return 0
    try:
        return max(int(value), 0)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return 0


def _iter_events(jsonl_path: str) -> Iterator[dict[str, Any]]:
    try:
        with open(jsonl_path, encoding="utf-8", errors="replace") as stream:
            for raw in stream:
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    event = json.loads(raw)
                except json.JSONDecodeError:
                    continue
                if isinstance(event, dict):
                    yield event
    except OSError:
        return


def _event_payload(event: dict[str, Any]) -> dict[str, Any]:
    """Flatten the common top-level event shape while tolerating ``data``."""
    payload = {key: value for key, value in event.items() if key != "type"}
    data = payload.pop("data", None)
    if isinstance(data, dict):
        payload.update(data)
    return payload


def _unwrap_tla_fence(response: str) -> str:
    """Unwrap a sole ``tla`` Markdown fence, leaving all other text unchanged."""
    matches = list(_FENCED_BLOCK.finditer(response))
    if len(matches) != 1 or response.count("```") != 2:
        return response
    match = matches[0]
    if response[: match.start()].strip() or response[match.end() :].strip():
        return response
    if match.group("language").strip().lower() != "tla":
        return response
    return match.group("body")


class OneShotBackend(Backend):
    """Sibling backend approach for one audited, tool-free model request."""

    provider: str = ""
    model: str
    approach = "one_shot"
    capabilities = BackendCapabilities(
        model_preflight=False,
        default_infra_retries=0,
        max_infra_retries=0,
        max_continuations=0,
    )

    @staticmethod
    def _is_exact_count(value: object, expected: int) -> bool:
        return isinstance(value, int) and not isinstance(value, bool) and value == expected

    @staticmethod
    def _is_exact_bool(value: object, expected: bool) -> bool:
        return value is expected

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        runner = (
            ["python3", "/opt/oneshot_runner.py"]
            if workspace == "/workspace"
            else [sys.executable, "-m", "evaluator.backends.oneshot_runner"]
        )
        return [
            *runner,
            "--provider",
            self.provider,
            "--workspace",
            workspace,
            "--result-dir",
            result_dir,
            "--model",
            self.model,
        ]

    def build_run_command(self, workspace: str, result_dir: str, deadline: float | None) -> list[str]:
        command = self.build_command(workspace, result_dir)
        command.extend(("--deadline", f"{deadline:.6f}" if deadline is not None else "0"))
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
        return mode.build_one_shot_prompt(benchmark_path, dependencies)

    def initial_result_metadata(self) -> dict[str, object]:
        return {
            **super().initial_result_metadata(),
            "one_shot": True,
            "model_requests": 0,
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
                error=error or "one-shot request contract violation",
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
                error=error or f"one-shot run ended with {termination_reason}",
            )

        materialized = self.materialize_solution(jsonl_path, destination)
        metadata: dict[str, object] = {"materialized": materialized}
        if not materialized:
            message = "one-shot response could not be uniquely materialized"
            metadata["materialization_error"] = message
            return SubmissionPlan(
                disposition=SubmissionDisposition.FAIL,
                copy_solution=False,
                error=message,
                metadata=metadata,
            )
        return SubmissionPlan(copy_solution=True, metadata=metadata)

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        lines: list[str] = []
        input_tokens = 0
        output_tokens = 0

        for event in _iter_events(jsonl_path):
            event_type = event.get("type")
            payload = _event_payload(event)
            if event_type == "response":
                response = payload.get("text", "")
                if isinstance(response, str) and response:
                    lines.extend((f"[AGENT] {response}", ""))
            elif event_type == "usage":
                input_tokens += _as_nonnegative_int(payload.get("input_tokens"))
                output_tokens += _as_nonnegative_int(payload.get("output_tokens"))
            elif event_type == "error":
                message = payload.get("message", "")
                lines.extend((f"[ERROR] {message}", ""))

        return "\n".join(lines), input_tokens, output_tokens

    def materialize_solution(self, jsonl_path: str, destination: str) -> bool:
        """Atomically write the sole non-empty response for grader validation."""
        responses: list[object] = []
        for event in _iter_events(jsonl_path):
            if event.get("type") != "response":
                continue
            responses.append(_event_payload(event).get("text"))

        if len(responses) != 1 or not isinstance(responses[0], str) or not responses[0].strip():
            return False
        solution = _unwrap_tla_fence(responses[0])

        target = Path(destination)
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

    def parse_run_metadata(self, jsonl_path: str) -> dict[str, object]:
        """Return normalized, result-safe audit metadata from runner events."""
        metadata: dict[str, object] = {"one_shot": True}
        request_counts: list[int] = []
        saw_model_output = False

        for event in _iter_events(jsonl_path):
            event_type = event.get("type")
            payload = _event_payload(event)
            if event_type in {"response", "usage"}:
                saw_model_output = True

            if event_type == "error":
                message = payload.get("message")
                if isinstance(message, str) and message:
                    metadata["error"] = message

            if event_type in {"metadata", "request_audit", "result"}:
                metadata.update(payload)

            for key in _REQUEST_COUNT_KEYS:
                if key in payload:
                    request_counts.append(_as_nonnegative_int(payload[key]))
            requests = payload.get("requests")
            if isinstance(requests, list):
                request_counts.append(len(requests))

        for key in (*_REQUEST_COUNT_KEYS, "requests"):
            metadata.pop(key, None)
        metadata["one_shot"] = True
        metadata["model_requests"] = max(request_counts) if request_counts else int(saw_model_output)
        return metadata

    def validate_request_audit(self, audit: dict[str, object], request_count: int) -> bool:
        """Validate the provider-neutral strict request contract."""

        return (
            audit.get("provider") == self.provider
            and self._is_exact_count(audit.get("model_requests"), request_count)
            and audit.get("audit_scope") in {"adapter", "wire"}
            and audit.get("contract_ok") is True
            and self._is_exact_count(audit.get("request_attempts"), request_count)
            and self._is_exact_count(audit.get("blocked_requests"), 0)
            and audit.get("system_prompt_present") is False
            and audit.get("tools_present") is False
            and audit.get("retries_enabled") is False
        )
