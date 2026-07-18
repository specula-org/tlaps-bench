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

from .base import AgentBackend

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


class OneShotBackend(AgentBackend):
    """Common command, output, and materialization behavior for one-shot runs."""

    provider: str = ""
    model: str
    is_one_shot = True
    supports_model_preflight = False
    supports_continuations = False
    default_infra_retries = 0

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
