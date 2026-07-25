"""LiteLLM backend — evaluate any model via unified API."""

from __future__ import annotations

import json

from evaluator.usage import RequestUsage, UsageCost, UsageSummary, nonnegative_float, nonnegative_int

from .agentic import AgenticBackend
from .base import detect_firewall_hosts
from .litellm_common import (
    DEFAULT_MODEL,
    ENV_KEYS,
    REASONING_EFFORT_VALUES,
    check_auth,
    credential_mounts,
    uses_bedrock,
)


class LiteLLMBackend(AgenticBackend):
    name = "litellm"
    install_script = "install-litellm.sh"
    env_keys = ENV_KEYS
    reasoning_effort_values = REASONING_EFFORT_VALUES

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        return credential_mounts(self.model)

    def _uses_bedrock(self) -> bool:
        return uses_bedrock(self.model)

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        command = [
            "python3",
            "/opt/litellm_agent.py",
            "--workspace",
            workspace,
            "--model",
            self.model,
        ]
        if self.reasoning_effort is not None:
            command.extend(["--reasoning-effort", self.reasoning_effort])
        return command

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def check_auth(self) -> str | None:
        return check_auth(self.model, self.name)

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0

        try:
            with open(jsonl_path) as f:
                for raw in f:
                    raw = raw.strip()
                    if not raw:
                        continue
                    try:
                        event = json.loads(raw)
                    except json.JSONDecodeError:
                        continue

                    etype = event.get("type", "")
                    if etype == "response":
                        text = event.get("text", "")
                        if text:
                            lines.append(f"[AGENT] {text[:3000]}")
                            lines.append("")
                    elif etype == "usage":
                        in_tok += event.get("input_tokens", 0)
                        out_tok += event.get("output_tokens", 0)
                    elif etype == "error":
                        lines.append(f"[ERROR] {event.get('message', '')}")
                        lines.append("")
        except FileNotFoundError:
            pass

        return "\n".join(lines), in_tok, out_tok

    def parse_usage(self, jsonl_path: str, *, input_tokens: int, output_tokens: int) -> UsageSummary:
        requests: list[RequestUsage] = []
        warnings: list[str] = []
        aggregate_requests: int | None = None
        aggregate_input_tokens: int | None = None
        aggregate_output_tokens: int | None = None
        saw_aggregate = False
        saw_error = False

        try:
            with open(jsonl_path) as stream:
                for raw in stream:
                    raw = raw.strip()
                    if not raw:
                        continue
                    try:
                        event = json.loads(raw)
                    except json.JSONDecodeError:
                        continue
                    if not isinstance(event, dict):
                        continue
                    etype = event.get("type", "")

                    if etype == "request_usage":
                        costs: list[UsageCost] = []
                        raw_costs = event.get("costs")
                        if isinstance(raw_costs, list):
                            for raw_cost in raw_costs:
                                cost = UsageCost.from_dict(raw_cost)
                                if cost is not None:
                                    costs.append(cost)
                        finish_reason = event.get("finish_reason")
                        requests.append(
                            RequestUsage(
                                input_tokens=nonnegative_int(event.get("input_tokens")),
                                output_tokens=nonnegative_int(event.get("output_tokens")),
                                cache_read_input_tokens=nonnegative_int(event.get("cache_read_input_tokens")),
                                cache_write_input_tokens=nonnegative_int(event.get("cache_write_input_tokens")),
                                reasoning_output_tokens=nonnegative_int(event.get("reasoning_output_tokens")),
                                requested_model=self.model,
                                resolved_model=(event.get("model") if isinstance(event.get("model"), str) else None),
                                provider="litellm",
                                duration_secs=nonnegative_float(event.get("duration_secs")),
                                finish_reasons=(
                                    (finish_reason,) if isinstance(finish_reason, str) and finish_reason else ()
                                ),
                                request_id=(
                                    event.get("request_id") if isinstance(event.get("request_id"), str) else None
                                ),
                                costs=tuple(costs),
                            )
                        )
                    elif etype == "usage":
                        saw_aggregate = True
                        aggregate_requests = nonnegative_int(event.get("model_requests"))
                        aggregate_input_tokens = nonnegative_int(event.get("input_tokens"))
                        aggregate_output_tokens = nonnegative_int(event.get("output_tokens"))
                    elif etype == "error":
                        saw_error = True
        except FileNotFoundError:
            pass

        if not requests:
            # Only the legacy aggregate is present (older agent, or a run that
            # died before its first response).
            if input_tokens or output_tokens:
                legacy_warnings = ["per-request LiteLLM usage unavailable"]
                if saw_error:
                    legacy_warnings.append("LiteLLM stopped on a completion error; usage is a lower bound")
                return UsageSummary(
                    input_tokens=nonnegative_int(input_tokens),
                    output_tokens=nonnegative_int(output_tokens),
                    model_requests=aggregate_requests,
                    sources=("litellm_agent_legacy_event",),
                    available=True,
                    complete=False,
                    is_lower_bound=True,
                    warnings=tuple(legacy_warnings),
                )
            if saw_error:
                return UsageSummary(
                    model_requests=aggregate_requests,
                    sources=("litellm_agent_event",),
                    available=saw_aggregate,
                    complete=False,
                    is_lower_bound=True,
                    warnings=("LiteLLM stopped on a completion error; request usage is unavailable",),
                )
            if saw_aggregate and aggregate_requests == 0:
                if aggregate_input_tokens != 0 or aggregate_output_tokens != 0:
                    aggregate_warnings: list[str] = []
                    for field, value in (
                        ("input_tokens", aggregate_input_tokens),
                        ("output_tokens", aggregate_output_tokens),
                    ):
                        if value is None:
                            aggregate_warnings.append(f"LiteLLM aggregate {field} is unavailable")
                        elif value != 0:
                            aggregate_warnings.append(f"LiteLLM aggregate {field} {value} contradicts model_requests 0")
                    return UsageSummary(
                        input_tokens=aggregate_input_tokens,
                        output_tokens=aggregate_output_tokens,
                        model_requests=0,
                        sources=("litellm_agent_event",),
                        available=True,
                        complete=False,
                        is_lower_bound=True,
                        warnings=tuple(aggregate_warnings),
                    )
                return UsageSummary(
                    input_tokens=0,
                    output_tokens=0,
                    model_requests=0,
                    sources=("litellm_agent_event",),
                    available=True,
                    complete=True,
                )
            return UsageSummary(
                sources=("litellm_agent_event",),
                available=False,
                complete=False,
                warnings=("LiteLLM usage events unavailable",),
            )

        if aggregate_requests is not None and aggregate_requests != len(requests):
            warnings.append(
                f"LiteLLM aggregate model_requests {aggregate_requests} differs from per-request events {len(requests)}"
            )
        elif saw_aggregate and aggregate_requests is None:
            warnings.append("LiteLLM aggregate model_requests is unavailable")
        if saw_error:
            warnings.append("LiteLLM stopped on a completion error; usage covers completed requests only")
        if not saw_aggregate:
            warnings.append("LiteLLM aggregate usage event missing; usage is a lower bound")
        missing_input = sum(request.input_tokens is None for request in requests)
        missing_output = sum(request.output_tokens is None for request in requests)
        missing_cost = sum(not request.costs for request in requests)
        if missing_input:
            warnings.append(f"LiteLLM input tokens are unavailable for {missing_input} model request(s)")
        if missing_output:
            warnings.append(f"LiteLLM output tokens are unavailable for {missing_output} model request(s)")
        if missing_cost:
            warnings.append(f"LiteLLM cost is unavailable for {missing_cost} model request(s); total is a lower bound")
        if saw_aggregate:
            if aggregate_input_tokens is None:
                warnings.append("LiteLLM aggregate input_tokens is unavailable")
            elif not missing_input:
                request_input_tokens = sum(request.input_tokens or 0 for request in requests)
                if aggregate_input_tokens != request_input_tokens:
                    warnings.append(
                        f"LiteLLM aggregate input_tokens {aggregate_input_tokens} differs from "
                        f"per-request total {request_input_tokens}"
                    )
            if aggregate_output_tokens is None:
                warnings.append("LiteLLM aggregate output_tokens is unavailable")
            elif not missing_output:
                request_output_tokens = sum(request.output_tokens or 0 for request in requests)
                if aggregate_output_tokens != request_output_tokens:
                    warnings.append(
                        f"LiteLLM aggregate output_tokens {aggregate_output_tokens} differs from "
                        f"per-request total {request_output_tokens}"
                    )

        # The aggregate counts attempted calls, while request events exist only
        # for completed calls. Keep the strongest known count; a contradictory
        # smaller aggregate cannot erase completed-request evidence.
        attempted_requests = max(len(requests), aggregate_requests) if aggregate_requests is not None else len(requests)
        return UsageSummary.from_requests(
            requests,
            source="litellm_agent_event",
            complete=not warnings and saw_aggregate,
            is_lower_bound=bool(warnings),
            warnings=tuple(dict.fromkeys(warnings)),
            totals={"model_requests": attempted_requests},
        )
