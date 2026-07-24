"""Shared host-side contract for single-response model backends."""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
from collections.abc import Iterator
from contextlib import suppress
from dataclasses import replace
from pathlib import Path
from typing import Any

from evaluator.termination import TerminationContext, TerminationReason
from evaluator.usage import RequestUsage, UsageCost, UsageSummary, nonnegative_float, nonnegative_int

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
    """Sibling backend approach for one audited, tool-free model response."""

    provider: str = ""
    model: str
    approach = "one_shot"
    capabilities = BackendCapabilities(
        model_preflight=False,
        default_infra_retries=3,
        max_infra_retries=None,
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
        command = [
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
        if self.reasoning_effort is not None:
            command.extend(["--reasoning-effort", self.reasoning_effort])
        if self.max_output_tokens is not None:
            command.extend(["--max-output-tokens", str(self.max_output_tokens)])
        return command

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

    def parse_usage(self, jsonl_path: str, *, input_tokens: int, output_tokens: int) -> UsageSummary:
        payloads: list[dict[str, Any]] = []
        terminal_status: str | None = None
        terminal_model_requests: int | None = None
        saw_model_output = False
        for event in _iter_events(jsonl_path):
            event_type = event.get("type")
            payload = _event_payload(event)
            if event_type == "model_output_observed":
                saw_model_output = True
            elif event_type == "response":
                text = payload.get("text")
                saw_model_output = saw_model_output or (isinstance(text, str) and bool(text))
            elif event_type == "usage":
                payloads.append(payload)
            elif event_type == "result":
                status = payload.get("status")
                if isinstance(status, str):
                    terminal_status = status
                terminal_model_requests = nonnegative_int(payload.get("model_requests"))

        if not payloads:
            inferred_model_requests = (
                max(terminal_model_requests or 0, int(saw_model_output))
                if terminal_model_requests is not None or saw_model_output
                else None
            )
            if input_tokens or output_tokens:
                return UsageSummary(
                    input_tokens=nonnegative_int(input_tokens),
                    output_tokens=nonnegative_int(output_tokens),
                    model_requests=inferred_model_requests,
                    sources=(f"{self.provider}_oneshot_legacy_event",),
                    available=True,
                    complete=False,
                    is_lower_bound=True,
                    warnings=("structured one-shot usage event unavailable",),
                )
            if saw_model_output:
                return UsageSummary(
                    model_requests=inferred_model_requests,
                    sources=(f"{self.provider}_oneshot_model_output",),
                    available=True,
                    complete=False,
                    is_lower_bound=True,
                    warnings=("model request inferred from output evidence; structured usage unavailable",),
                )
            if terminal_model_requests == 0:
                return UsageSummary(
                    input_tokens=0,
                    output_tokens=0,
                    model_requests=0,
                    sources=(f"{self.provider}_oneshot_event",),
                    available=True,
                    complete=True,
                )
            return UsageSummary(
                model_requests=terminal_model_requests,
                sources=(f"{self.provider}_oneshot_event",),
                available=terminal_model_requests is not None,
                complete=False,
                warnings=("structured one-shot usage event unavailable",),
            )

        requests: list[RequestUsage] = []
        sources: list[str] = []
        runtime_versions: list[str] = []
        complete_flags: list[bool] = []
        lower_bound_flags: list[bool] = []
        reported_model_requests: list[int] = []
        usage_warnings: list[str] = []
        for payload in payloads:
            costs: list[UsageCost] = []
            raw_costs = payload.get("costs")
            if isinstance(raw_costs, list):
                for raw_cost in raw_costs:
                    if not isinstance(raw_cost, dict):
                        continue
                    amount = nonnegative_float(raw_cost.get("amount"))
                    unit = raw_cost.get("unit")
                    source = raw_cost.get("source")
                    if amount is not None and isinstance(unit, str) and unit and isinstance(source, str) and source:
                        costs.append(UsageCost(amount, unit, source))

            finish_reasons = payload.get("finish_reasons")
            if isinstance(finish_reasons, list):
                normalized_finish_reasons = tuple(
                    reason for reason in finish_reasons if isinstance(reason, str) and reason
                )
            else:
                finish_reason = payload.get("finish_reason")
                normalized_finish_reasons = (finish_reason,) if isinstance(finish_reason, str) and finish_reason else ()
            requests.append(
                RequestUsage(
                    input_tokens=nonnegative_int(payload.get("input_tokens")),
                    output_tokens=nonnegative_int(payload.get("output_tokens")),
                    cache_read_input_tokens=nonnegative_int(payload.get("cache_read_input_tokens")),
                    cache_write_input_tokens=nonnegative_int(payload.get("cache_write_input_tokens")),
                    reasoning_output_tokens=nonnegative_int(payload.get("reasoning_output_tokens")),
                    requested_model=self.model,
                    resolved_model=payload.get("model") if isinstance(payload.get("model"), str) else None,
                    provider=self.provider,
                    endpoint=payload.get("endpoint") if isinstance(payload.get("endpoint"), str) else None,
                    duration_secs=nonnegative_float(payload.get("duration_secs")),
                    finish_reasons=normalized_finish_reasons,
                    request_id=payload.get("request_id") if isinstance(payload.get("request_id"), str) else None,
                    provider_request_id=(
                        payload.get("provider_request_id")
                        if isinstance(payload.get("provider_request_id"), str)
                        else None
                    ),
                    costs=tuple(costs),
                )
            )
            source = payload.get("source")
            if isinstance(source, str) and source:
                sources.append(source)
            runtime_version = payload.get("runtime_version")
            if isinstance(runtime_version, str) and runtime_version:
                runtime_versions.append(runtime_version)
            model_requests = nonnegative_int(payload.get("model_requests"))
            copilot_cost_missing = self.provider == "copilot" and model_requests != 0 and not costs
            explicit_complete = payload.get("complete")
            declared_complete = (
                explicit_complete if isinstance(explicit_complete, bool) else terminal_status == "success"
            )
            complete_flags.append(declared_complete and not copilot_cost_missing)
            explicit_lower_bound = payload.get("is_lower_bound")
            declared_lower_bound = (
                explicit_lower_bound
                if isinstance(explicit_lower_bound, bool)
                else terminal_status in {"error", "timeout"}
            )
            lower_bound_flags.append(declared_lower_bound or copilot_cost_missing)
            if copilot_cost_missing:
                usage_warnings.append("Copilot usage cost unavailable; total cost is a lower bound")
            if model_requests is not None:
                reported_model_requests.append(model_requests)

        totals: dict[str, object] = {}
        if reported_model_requests:
            totals["model_requests"] = sum(reported_model_requests)

        usage = UsageSummary.from_requests(
            requests,
            source=sources[0] if sources else f"{self.provider}_oneshot_event",
            complete=all(complete_flags),
            is_lower_bound=any(lower_bound_flags),
            runtime_versions=tuple(dict.fromkeys(runtime_versions)),
            warnings=tuple(dict.fromkeys(usage_warnings)),
            totals=totals,
        )
        if len(set(sources)) > 1:
            usage = replace(usage, sources=tuple(dict.fromkeys(sources)))
        if terminal_model_requests is not None and (usage.model_requests or 0) > terminal_model_requests:
            return UsageSummary(
                model_requests=terminal_model_requests,
                sources=tuple(dict.fromkeys(sources)) or (f"{self.provider}_oneshot_event",),
                runtime_versions=tuple(dict.fromkeys(runtime_versions)),
                available=True,
                complete=False,
                is_lower_bound=True,
                warnings=("usage records exceed audited model requests; token and cost totals discarded",),
            )
        if terminal_model_requests is not None and terminal_model_requests > (usage.model_requests or 0):
            missing = terminal_model_requests - (usage.model_requests or 0)
            usage = replace(
                usage,
                model_requests=terminal_model_requests,
                complete=False,
                is_lower_bound=True,
                warnings=(
                    *usage.warnings,
                    f"usage unavailable for {missing} forwarded model request(s)",
                ),
            )
        if saw_model_output and (usage.model_requests or 0) < 1:
            usage = replace(
                usage,
                model_requests=1,
                complete=False,
                is_lower_bound=True,
                warnings=(*usage.warnings, "model request inferred from output evidence"),
            )
        return usage

    def is_infra_retryable(self, ctx: TerminationContext) -> bool:
        """Replay only empty startups or explicitly transient terminal errors."""

        events = ctx.events()
        if not ctx.event_stream_valid():
            return False
        if not events:
            return ctx.agent_exit not in {None, 0}

        for event in events:
            event_type = event.get("type")
            if event_type == "model_output_observed":
                return False
            if event_type == "response":
                text = _event_payload(event).get("text")
                if isinstance(text, str) and text:
                    return False

        audits = [_event_payload(event) for event in events if event.get("type") == "request_audit"]
        results = [_event_payload(event) for event in events if event.get("type") == "result"]
        if len(audits) != 1 or len(results) != 1:
            return False
        terminal = results[0]
        return terminal.get("status") == "error" and terminal.get("retryable") is True

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
            if event_type == "model_output_observed":
                saw_model_output = True
            elif event_type == "response":
                text = payload.get("text")
                saw_model_output = saw_model_output or (isinstance(text, str) and bool(text))
            elif event_type == "usage":
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
        metadata["model_requests"] = max([int(saw_model_output), *request_counts])
        return metadata

    def validate_request_audit(self, audit: dict[str, object], request_count: int) -> bool:
        """Validate the provider-neutral one-shot contract."""

        return (
            audit.get("provider") == self.provider
            and self._is_exact_count(audit.get("model_requests"), request_count)
            and audit.get("audit_scope") in {"adapter", "wire"}
            and audit.get("contract_ok") is True
            and self._is_exact_count(audit.get("request_attempts"), request_count)
            and self._is_exact_count(audit.get("blocked_requests"), 0)
            and audit.get("system_prompt_present") is False
            and audit.get("tools_present") is False
        )
