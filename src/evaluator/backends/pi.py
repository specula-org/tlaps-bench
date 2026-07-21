"""Pi coding agent backend."""

from __future__ import annotations

import json
import math
import os
import shlex
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from evaluator.usage import RequestUsage, UsageCost, UsageSummary

from .agentic import AgenticBackend
from .base import (
    detect_firewall_hosts,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
)

DEFAULT_MODEL = "openai/gpt-5.5"

_PI_USAGE_SOURCE = "pi_cli_message_end"
_PI_COST_SOURCE = "pi.usage.cost.total"
_PI_STOP_REASONS = frozenset({"stop", "length", "toolUse", "error", "aborted"})
_PI_NON_ASSISTANT_MESSAGE_ROLES = frozenset(
    {"user", "toolResult", "bashExecution", "custom", "branchSummary", "compactionSummary"}
)
_PI_RUN_ACTIVITY_EVENTS = frozenset(
    {
        "agent_start",
        "agent_end",
        "turn_start",
        "turn_end",
        "message_start",
        "message_update",
        "message_end",
        "tool_execution_start",
        "tool_execution_update",
        "tool_execution_end",
        "compaction_start",
        "compaction_end",
    }
)


@dataclass(frozen=True)
class _ParsedPiRequest:
    request: RequestUsage | None
    incomplete: bool
    warnings: tuple[str, ...]


@dataclass(frozen=True)
class _ParsedPiRun:
    transcript: str
    usage: UsageSummary
    model_activity: bool


def _strict_token(value: object) -> int | None:
    """Validate a native Pi token field without coercion."""

    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else None


def _strict_cost(value: object) -> float | None:
    """Validate Pi's native USD estimate without accepting booleans or non-finite values."""

    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return None
    parsed = float(value)
    return parsed if parsed >= 0 and math.isfinite(parsed) else None


def _text(value: object) -> str | None:
    return value if isinstance(value, str) and bool(value.strip()) else None


def _parse_assistant_request(message: dict[str, Any]) -> _ParsedPiRequest:
    """Convert one finalized native assistant message into provider-neutral usage."""

    raw_usage = message.get("usage")
    if not isinstance(raw_usage, dict):
        return _ParsedPiRequest(None, True, ("Pi assistant message has no usage object",))

    token_names = ("input", "output", "cacheRead", "cacheWrite", "totalTokens")
    tokens = {name: _strict_token(raw_usage.get(name)) for name in token_names}
    invalid_tokens = [name for name in token_names if tokens[name] is None]
    if invalid_tokens:
        return _ParsedPiRequest(
            None,
            True,
            (f"Pi assistant usage has invalid core fields: {', '.join(invalid_tokens)}",),
        )

    input_tokens = tokens["input"]
    output_tokens = tokens["output"]
    cache_read_tokens = tokens["cacheRead"]
    cache_write_tokens = tokens["cacheWrite"]
    total_tokens = tokens["totalTokens"]
    assert input_tokens is not None
    assert output_tokens is not None
    assert cache_read_tokens is not None
    assert cache_write_tokens is not None
    assert total_tokens is not None

    if input_tokens == output_tokens == cache_read_tokens == cache_write_tokens == 0:
        # Pi uses an all-zero usage object for failures where no trustworthy
        # provider accounting was returned. It is not proof of a free request.
        return _ParsedPiRequest(None, True, ("Pi reported an untrustworthy all-zero usage placeholder",))

    warnings: list[str] = []
    incomplete = False
    expected_total = input_tokens + output_tokens + cache_read_tokens + cache_write_tokens
    if total_tokens != expected_total:
        warnings.append(
            f"Pi totalTokens mismatch: reported {total_tokens}, expected {expected_total} from component fields"
        )
        incomplete = True

    reasoning_tokens = None
    if "reasoning" in raw_usage:
        reasoning_tokens = _strict_token(raw_usage["reasoning"])
        if reasoning_tokens is None:
            warnings.append("Pi assistant usage has invalid reasoning tokens")
            incomplete = True
        elif reasoning_tokens > output_tokens:
            warnings.append("Pi reasoning output tokens exceed total output tokens")
            reasoning_tokens = None
            incomplete = True

    costs: tuple[UsageCost, ...] = ()
    raw_cost = raw_usage.get("cost")
    cost_total = _strict_cost(raw_cost.get("total")) if isinstance(raw_cost, dict) else None
    if cost_total is None:
        warnings.append("Pi assistant usage has missing or invalid cost.total")
        incomplete = True
    else:
        costs = (UsageCost(amount=cost_total, unit="usd", source=_PI_COST_SOURCE),)
        if total_tokens > 0 and cost_total == 0:
            warnings.append(
                "Pi reported nonzero tokens with a zero USD estimate; model pricing metadata may be zero or unavailable"
            )

    requested_model = _text(message.get("model"))
    provider = _text(message.get("provider"))
    endpoint = _text(message.get("api"))
    for field, value in (("model", requested_model), ("provider", provider), ("api", endpoint)):
        if value is None:
            warnings.append(f"Pi assistant message has missing or invalid {field}")
            incomplete = True

    resolved_model = requested_model
    if "responseModel" in message:
        response_model = _text(message["responseModel"])
        if response_model is None:
            warnings.append("Pi assistant message has invalid responseModel")
            incomplete = True
        else:
            resolved_model = response_model

    provider_request_id = None
    if "responseId" in message:
        provider_request_id = _text(message["responseId"])
        if provider_request_id is None:
            warnings.append("Pi assistant message has invalid responseId")
            incomplete = True

    raw_stop_reason = message.get("stopReason")
    finish_reasons: tuple[str, ...] = ()
    if isinstance(raw_stop_reason, str) and raw_stop_reason in _PI_STOP_REASONS:
        finish_reasons = (raw_stop_reason,)
    else:
        warnings.append("Pi assistant message has missing or invalid stopReason")
        incomplete = True

    # Pi defines input as non-cached input, while the benchmark schema defines
    # input as the complete input total. cacheWrite1h is already a subset of
    # cacheWrite and must not be added again here (or to Pi's native cost).
    request = RequestUsage(
        input_tokens=input_tokens + cache_read_tokens + cache_write_tokens,
        output_tokens=output_tokens,
        cache_read_input_tokens=cache_read_tokens,
        cache_write_input_tokens=cache_write_tokens,
        reasoning_output_tokens=reasoning_tokens,
        requested_model=requested_model,
        resolved_model=resolved_model,
        provider=provider,
        endpoint=endpoint,
        finish_reasons=finish_reasons,
        provider_request_id=provider_request_id,
        costs=costs,
    )
    return _ParsedPiRequest(request, incomplete, tuple(warnings))


def _append_transcript_event(lines: list[str], event: dict[str, Any]) -> None:
    if event.get("type") != "message_update":
        return
    update = event.get("assistantMessageEvent")
    if not isinstance(update, dict) or update.get("type") != "text_delta":
        return
    delta = update.get("delta")
    if isinstance(delta, str) and delta:
        lines.append(delta)


def _has_all_zero_usage_placeholder(message: dict[str, Any]) -> bool:
    usage = message.get("usage")
    if not isinstance(usage, dict):
        return False
    for name in ("input", "output", "cacheRead", "cacheWrite", "totalTokens"):
        if _strict_token(usage.get(name)) != 0:
            return False
    raw_cost = usage.get("cost")
    cost_total = _strict_cost(raw_cost.get("total")) if isinstance(raw_cost, dict) else None
    return cost_total == 0


def _is_pre_stream_exception_fallback(message: dict[str, Any]) -> bool:
    """Match agent-core's exact fallback when no provider stream was returned."""

    content = message.get("content")
    if not isinstance(content, list) or len(content) != 1:
        return False
    block = content[0]
    stop_reason = message.get("stopReason")
    return (
        isinstance(block, dict)
        and block.get("type") == "text"
        and block.get("text") == ""
        and _has_all_zero_usage_placeholder(message)
        and isinstance(stop_reason, str)
        and stop_reason in {"error", "aborted"}
        and _text(message.get("errorMessage")) is not None
    )


def _event_proves_model_activity(event: dict[str, Any]) -> bool:
    """Recognize native activity that makes a replacement launch unsafe."""

    event_type = event.get("type")
    if not isinstance(event_type, str):
        # A schema-invalid discriminator may hide an activity event.
        return True
    if event_type in {"tool_execution_start", "tool_execution_update", "tool_execution_end"}:
        # Agent-core tool execution can only follow an assistant tool call. It
        # therefore preserves paid-work evidence even if that assistant event
        # was the part of a damaged stream that went missing.
        return True
    if event_type == "compaction_start":
        # Compaction calls a summarizer model, but Pi does not include that
        # request's usage in its JSON events or session totals.
        return True
    if event_type == "message_update":
        # Pi emits message_update only for a streaming assistant response.
        return True
    if event_type not in {"message_start", "message_end"}:
        return False
    message = event.get("message")
    if not isinstance(message, dict):
        return True
    role = message.get("role")
    if role != "assistant":
        # Known non-assistant lifecycle messages do not imply a provider call.
        # An absent or future role is unsafe because the corrupted candidate may
        # have been an assistant event whose paid-work evidence was lost.
        return not isinstance(role, str) or role not in _PI_NON_ASSISTANT_MESSAGE_ROLES
    # agent-core constructs the recognized fallback only when getApiKey,
    # context conversion, or stream creation throws before returning a provider
    # stream. Provider adapters use an empty content array for their own errors,
    # including ambiguous post-dispatch transport failures.
    # Every other assistant lifecycle event came from a provider stream or is
    # too damaged to prove otherwise. Missing usage is not evidence of no work.
    return not _is_pre_stream_exception_fallback(message)


def _parse_pi_run(jsonl_path: str) -> _ParsedPiRun:
    transcript_parts: list[str] = []
    requests: list[RequestUsage] = []
    warnings: list[str] = []
    malformed_lines = 0
    invalid_event_types = 0
    invalid_candidates = 0
    settled = False
    compacted = False
    activity_after_settled = False
    model_activity = False
    read_error: Exception | None = None

    try:
        with open(jsonl_path) as f:
            for raw in f:
                raw = raw.strip()
                if not raw:
                    continue
                try:
                    event = json.loads(raw)
                except json.JSONDecodeError:
                    malformed_lines += 1
                    continue
                if not isinstance(event, dict):
                    malformed_lines += 1
                    continue

                event_type = event.get("type")
                if not isinstance(event_type, str):
                    invalid_event_types += 1
                    model_activity = True
                    continue
                _append_transcript_event(transcript_parts, event)
                model_activity = model_activity or _event_proves_model_activity(event)
                if settled and event_type in _PI_RUN_ACTIVITY_EVENTS:
                    activity_after_settled = True
                if event_type == "agent_settled":
                    settled = True
                elif event_type == "compaction_start":
                    compacted = True
                elif event_type == "message_end":
                    message = event.get("message")
                    if not isinstance(message, dict):
                        invalid_candidates += 1
                        warnings.append("Pi message_end event has no message object")
                        continue
                    role = message.get("role")
                    if role != "assistant":
                        if not isinstance(role, str) or role not in _PI_NON_ASSISTANT_MESSAGE_ROLES:
                            invalid_candidates += 1
                            warnings.append("Pi message_end event has missing or invalid message role")
                        continue
                    parsed_request = _parse_assistant_request(message)
                    warnings.extend(parsed_request.warnings)
                    if parsed_request.request is None:
                        invalid_candidates += 1
                    else:
                        requests.append(parsed_request.request)
                        if parsed_request.incomplete:
                            invalid_candidates += 1
    except (OSError, UnicodeError) as exc:
        read_error = exc

    if read_error is not None:
        warnings.append(f"Pi JSONL output unavailable or truncated: {type(read_error).__name__}")
    if malformed_lines:
        warnings.append(f"Pi JSONL contains {malformed_lines} malformed nonempty line(s)")
    if invalid_event_types:
        warnings.append(f"Pi JSONL contains {invalid_event_types} event(s) with missing or invalid type")
    if (
        malformed_lines
        or invalid_event_types
        or (read_error is not None and not isinstance(read_error, FileNotFoundError))
    ):
        # A nonempty native line that cannot be decoded may itself have been an
        # assistant activity event. Likewise, an existing stream that cannot be
        # read gives us no safe evidence that the provider was never called.
        # A genuinely absent startup artifact remains eligible for replacement.
        model_activity = True
    if compacted:
        warnings.append(
            "Pi performed context compaction; summarizer model usage is not exposed by JSON mode, "
            "so totals are a lower bound"
        )
    if activity_after_settled:
        warnings.append("Pi JSONL contains run activity after agent_settled")

    if not requests:
        if settled:
            warnings.append("Pi agent settled without trustworthy assistant usage")
        else:
            warnings.append("Pi assistant usage is unavailable before agent_settled")
        return _ParsedPiRun(
            transcript="".join(transcript_parts),
            usage=UsageSummary(
                sources=("pi_cli_jsonl",),
                available=False,
                warnings=tuple(dict.fromkeys(warnings)),
            ),
            model_activity=model_activity,
        )

    lower_bound = bool(
        read_error
        or malformed_lines
        or invalid_event_types
        or invalid_candidates
        or compacted
        or activity_after_settled
        or not settled
    )
    if not settled:
        warnings.append("Pi agent_settled was not observed; recorded usage may be partial")
    usage = UsageSummary.from_requests(
        requests,
        source=_PI_USAGE_SOURCE,
        complete=not lower_bound,
        is_lower_bound=lower_bound,
        warnings=tuple(dict.fromkeys(warnings)),
    )
    return _ParsedPiRun(
        transcript="".join(transcript_parts),
        usage=usage,
        model_activity=model_activity,
    )


class PiBackend(AgenticBackend):
    name = "pi"
    install_script = "install-pi.sh"
    session_state_dir = "/root/.pi"
    env_keys = [
        "ANTHROPIC_API_KEY",
        "ANTHROPIC_OAUTH_TOKEN",
        "AWS_ACCESS_KEY_ID",
        "AWS_SECRET_ACCESS_KEY",
        "AWS_DEFAULT_REGION",
        "AWS_REGION",
        "AWS_PROFILE",
        "AWS_BEARER_TOKEN_BEDROCK",
        "COPILOT_GITHUB_TOKEN",
        "GH_TOKEN",
        "GITHUB_TOKEN",
        "GEMINI_API_KEY",
        "GOOGLE_GENERATIVE_AI_API_KEY",
        "GOOGLE_APPLICATION_CREDENTIALS",
        "GOOGLE_CLOUD_PROJECT",
        "GOOGLE_CLOUD_LOCATION",
        "GOOGLE_GENAI_USE_VERTEXAI",
        "GOOGLE_API_KEY",
        "GROQ_API_KEY",
        "HF_TOKEN",
        "MISTRAL_API_KEY",
        "OPENAI_API_KEY",
        "OPENROUTER_API_KEY",
        "XAI_API_KEY",
    ]
    reasoning_effort_values = ("off", "minimal", "low", "medium", "high", "xhigh", "max")

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        provider, _ = self._provider_model()
        if provider == "amazon-bedrock" and not has_aws_env_credentials():
            return ["aws"]
        if not self._has_env_auth(provider) and self._host_auth_has_provider(provider):
            return ["pi"]
        return []

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        provider, model = self._provider_model()
        thinking_option = (
            f"--thinking {shlex.quote(self.reasoning_effort)} " if self.reasoning_effort is not None else ""
        )
        return [
            "bash",
            "-lc",
            (
                "prompt=$(cat); "
                f"cd {shlex.quote(workspace)}; "
                "pi --mode json --no-session "
                f"{thinking_option}"
                f"--provider {shlex.quote(provider)} --model {shlex.quote(model)} "
                '"$prompt"'
            ),
        ]

    def check_auth(self) -> str | None:
        provider, _ = self._provider_model()
        if provider == "amazon-bedrock":
            if has_aws_env_credentials():
                if not has_aws_region():
                    return "pi: AWS_REGION or AWS_DEFAULT_REGION required for amazon-bedrock env auth"
                return None
            if has_aws_shared_credentials():
                return None
            return "pi: AWS credentials not found for amazon-bedrock provider"

        required_env = self._required_env(provider)

        if required_env is None or self._host_auth_has_provider(provider):
            return None
        if self._has_env_auth(provider):
            return None
        return f"pi: none of {', '.join(required_env)} set for {provider} provider"

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        parsed = _parse_pi_run(jsonl_path)
        return parsed.transcript, parsed.usage.legacy_input_tokens, parsed.usage.legacy_output_tokens

    def parse_usage(self, jsonl_path: str, *, input_tokens: int, output_tokens: int) -> UsageSummary:
        # Legacy totals come from this same native event interpretation, so the
        # compatibility fields cannot omit cache writes or diverge from usage.
        del input_tokens, output_tokens
        return _parse_pi_run(jsonl_path).usage

    def retry_may_duplicate_model_work(self, jsonl_path: str) -> bool:
        # Pi emits final usage only at message_end. Native assistant-stream or
        # compaction activity proves a model call may already have happened even
        # when a failed/truncated launch never reached that accounting event.
        return _parse_pi_run(jsonl_path).model_activity

    def _provider_model(self) -> tuple[str, str]:
        if "/" not in self.model:
            raise ValueError("pi model must be in provider/model format")
        return self.model.split("/", 1)

    @staticmethod
    def _required_env(provider: str) -> list[str] | None:
        return {
            "anthropic": ["ANTHROPIC_OAUTH_TOKEN", "ANTHROPIC_API_KEY"],
            "github-copilot": ["COPILOT_GITHUB_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"],
            "google": ["GEMINI_API_KEY", "GOOGLE_GENERATIVE_AI_API_KEY", "GOOGLE_API_KEY"],
            "groq": ["GROQ_API_KEY"],
            "huggingface": ["HF_TOKEN"],
            "mistral": ["MISTRAL_API_KEY"],
            "openai": ["OPENAI_API_KEY"],
            "openai-codex": ["OPENAI_API_KEY"],
            "openrouter": ["OPENROUTER_API_KEY"],
            "xai": ["XAI_API_KEY"],
        }.get(provider)

    def _has_env_auth(self, provider: str) -> bool:
        required_env = self._required_env(provider)
        return bool(required_env and any(os.environ.get(key) for key in required_env))

    @staticmethod
    def _host_auth_has_provider(provider: str) -> bool:
        auth_path = Path.home() / ".pi" / "agent" / "auth.json"
        if auth_path.is_symlink():
            return False
        try:
            with open(auth_path) as f:
                auth = json.load(f)
        except (FileNotFoundError, OSError, json.JSONDecodeError):
            return False
        return isinstance(auth, dict) and provider in auth
