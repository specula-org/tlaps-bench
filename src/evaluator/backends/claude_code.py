"""Anthropic Claude Code CLI backend."""

from __future__ import annotations

import json
import os
import subprocess
from typing import Any

from evaluator.usage import RequestUsage, UsageCost, UsageSummary, nonnegative_float, nonnegative_int

from .agentic import AgenticBackend
from .base import (
    detect_firewall_hosts,
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "claude-opus-4-8"
PROVIDER = "anthropic"


def _optional_str(value: object) -> str | None:
    return value if isinstance(value, str) and value else None


def _message_usage(usage: object) -> tuple[int | None, int | None, int | None, int | None]:
    """Return ``(input, cache_read, cache_write, output)`` for one message.

    Anthropic reports cache reads/creations as buckets *beside* ``input_tokens``,
    but the shared usage contract treats them as classifications *within* input
    usage. Fold them in exactly once so ``input_tokens`` is the full billable
    input and the cache fields only classify part of it.
    """

    if not isinstance(usage, dict):
        return None, None, None, None
    base_input = nonnegative_int(usage.get("input_tokens"))
    cache_write = nonnegative_int(usage.get("cache_creation_input_tokens"))
    cache_read = nonnegative_int(usage.get("cache_read_input_tokens"))
    known_input = [value for value in (base_input, cache_write, cache_read) if value is not None]
    total_input = sum(known_input) if known_input else None
    return total_input, cache_read, cache_write, nonnegative_int(usage.get("output_tokens"))


def _streamed_request(message: dict[str, Any], requested_model: str | None, *, trust_output: bool) -> RequestUsage:
    """One per-request record from a deduplicated ``assistant`` event.

    A streamed message's input and cache counts are final, but its
    ``output_tokens`` is only the partial known at message start, so it is kept
    only when no authoritative ``result`` total is available.
    """

    total_input, cache_read, cache_write, output = _message_usage(message.get("usage"))
    stop_reason = _optional_str(message.get("stop_reason"))
    return RequestUsage(
        input_tokens=total_input,
        output_tokens=output if trust_output else None,
        cache_read_input_tokens=cache_read,
        cache_write_input_tokens=cache_write,
        requested_model=requested_model,
        resolved_model=_optional_str(message.get("model")),
        provider=PROVIDER,
        finish_reasons=((stop_reason,) if stop_reason is not None else ()),
        request_id=_optional_str(message.get("id")),
    )


def parse_claude_code_usage(jsonl_path: str, *, requested_model: str | None = None) -> UsageSummary | None:
    """Parse Claude Code stream-json usage into an authoritative usage record.

    Streamed ``assistant`` input/cache are final, but streamed ``output_tokens``
    is a message-start partial, so the settled output and USD cost are taken from
    the terminal ``result`` event. Without a result event the streamed sums are a
    lower bound.
    """

    streamed: list[dict[str, Any]] = []
    warnings: list[str] = []
    result_seen = False
    result_error = False
    result_totals: dict[str, int | None] = {}
    result_costs: list[UsageCost] = []
    model_time_secs: float | None = None
    num_turns: int | None = None
    # One `assistant` event is streamed per content block, each repeating the
    # turn's whole usage, so collapse to the first event per message id.
    seen_message_ids: set[str] = set()

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

                if etype == "assistant":
                    message = event.get("message")
                    if not isinstance(message, dict) or not isinstance(message.get("usage"), dict):
                        continue
                    message_id = _optional_str(message.get("id"))
                    if message_id is not None:
                        if message_id in seen_message_ids:
                            continue
                        seen_message_ids.add(message_id)
                    streamed.append(message)

                elif etype == "result":
                    result_seen = True
                    result_error = event.get("is_error") is True
                    total_input, cache_read, cache_write, output = _message_usage(event.get("usage"))
                    result_totals = {
                        "input_tokens": total_input,
                        "output_tokens": output,
                        "cache_read_input_tokens": cache_read,
                        "cache_write_input_tokens": cache_write,
                    }
                    num_turns = nonnegative_int(event.get("num_turns"))
                    total_cost = nonnegative_float(event.get("total_cost_usd"))
                    if total_cost is not None:
                        result_costs.append(UsageCost(total_cost, "usd", "claude_code.total_cost_usd"))
                    api_ms = nonnegative_float(event.get("duration_api_ms"))
                    if api_ms is not None:
                        model_time_secs = api_ms / 1000
    except FileNotFoundError:
        return None

    if not streamed and not result_seen:
        return None

    requests = [_streamed_request(message, requested_model, trust_output=not result_seen) for message in streamed]

    totals: dict[str, object] = {}
    input_discrepancy = False
    if result_seen:
        for field, value in result_totals.items():
            if value is not None:
                totals[field] = value
        if result_costs:
            totals["costs"] = tuple(result_costs)
        else:
            warnings.append("Claude Code result event did not report total_cost_usd")
        if model_time_secs is not None:
            totals["model_time_secs"] = model_time_secs
        if not streamed and num_turns is not None:
            totals["model_requests"] = num_turns

        # Input and cache are reliable per message, so a mismatch against the
        # authoritative result totals means streamed turns were lost.
        for field in ("input_tokens", "cache_read_input_tokens", "cache_write_input_tokens"):
            summary_total = result_totals.get(field)
            observed = sum(getattr(request, field) for request in requests if getattr(request, field) is not None)
            if streamed and summary_total is not None and observed != summary_total:
                input_discrepancy = True
                warnings.append(
                    f"Claude Code {field} result total {summary_total} differs from streamed total {observed}"
                )
    else:
        warnings.append("Claude Code result event missing; usage is a lower bound")

    return UsageSummary.from_requests(
        requests,
        source="claude_code_stream_json",
        complete=result_seen and not result_error and not input_discrepancy and bool(result_costs),
        is_lower_bound=not result_seen or result_error or input_discrepancy,
        warnings=tuple(dict.fromkeys(warnings)),
        totals=totals,
    )


class ClaudeCodeBackend(AgenticBackend):
    name = "claude_code"
    install_script = "install-claudecode.sh"
    session_state_dir = "/root/.claude"
    env_keys = [
        "ANTHROPIC_API_KEY",
        "CLAUDE_CODE_USE_BEDROCK",
        "CLAUDE_CODE_USE_MANTLE",
        "AWS_BEARER_TOKEN_BEDROCK",
        "AWS_REGION",
        "AWS_DEFAULT_REGION",
        "AWS_PROFILE",
        "ANTHROPIC_BEDROCK_BASE_URL",
        "ANTHROPIC_AWS_BASE_URL",
        "ANTHROPIC_SMALL_FAST_MODEL_AWS_REGION",
        "DISABLE_PROMPT_CACHING",
    ]

    # Tools the agent is allowed to use (mirrors SREGym's whitelist).
    # Using --allowedTools instead of --dangerously-skip-permissions
    # because the latter is blocked when running as root in containers.
    ALLOWED_TOOLS = [
        "Bash",
        "Edit",
        "Write",
        "Read",
        "Glob",
        "Grep",
        "LS",
        "NotebookEdit",
        "NotebookRead",
        "TodoRead",
        "TodoWrite",
        "Agent",
        "Skill",
        "SlashCommand",
        "Task",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        if self._uses_aws_provider() and needs_aws_shared_credentials():
            return ["aws"]
        if not self._uses_aws_provider() and self._needs_claude_credentials():
            return ["claude"]
        return []

    @staticmethod
    def _uses_aws_provider() -> bool:
        return (
            os.environ.get("CLAUDE_CODE_USE_BEDROCK", "").strip() == "1"
            or os.environ.get("CLAUDE_CODE_USE_MANTLE", "").strip() == "1"
        )

    @staticmethod
    def _needs_claude_credentials() -> bool:
        return not (os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"))

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        return [
            "claude",
            "--print",
            "--no-session-persistence",
            "--output-format",
            "stream-json",
            "--verbose",
            "--effort",
            "max",
            "--model",
            self.model,
            "--allowedTools",
        ] + self.ALLOWED_TOOLS

    def check_auth(self) -> str | None:
        if self._uses_aws_provider():
            if has_aws_bedrock_bearer_token():
                if not has_aws_region():
                    return "claude_code: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock bearer-token auth"
                return None
            if has_aws_env_credentials():
                if not has_aws_region():
                    return "claude_code: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock AWS env auth"
                return None
            if has_aws_shared_credentials():
                return None
            return "claude_code: Bedrock/Mantle selected but no AWS credentials detected"
        # Fast path: env var present.
        if os.environ.get("ANTHROPIC_API_KEY"):
            return None
        # Slow path: probe the CLI with --no-session-persistence so the
        # probe doesn't pollute the user's resume history. This makes one
        # tiny API call but covers OAuth / subscription auth that env-var
        # checks can't see.
        try:
            r = subprocess.run(
                ["claude", "--print", "--no-session-persistence", "--output-format", "text", "ok"],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if r.returncode == 0:
                return None
            stderr = (r.stderr or r.stdout or "").strip()
            if len(stderr) > 300:
                stderr = stderr[:300] + "..."
            return f"claude_code: auth probe failed (exit {r.returncode}): {stderr}"
        except subprocess.TimeoutExpired:
            return "claude_code: auth probe timed out (>30s)"
        except FileNotFoundError:
            return "claude_code: `claude` CLI not found on PATH"
        except Exception as e:
            return f"claude_code: auth probe error: {e}"

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def usage_script(self) -> str | None:
        return "scripts/usage/claude.sh"

    def default_quota(self) -> tuple[float, float]:
        return (80.0, 95.0)

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0
        final_in = None
        final_out = None
        # A turn's usage is echoed on every content-block event; count each once.
        counted_message_ids: set[str] = set()

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

                    if etype == "assistant":
                        message = event.get("message", {})
                        content = message.get("content", [])
                        if isinstance(content, list):
                            for block in content:
                                if not isinstance(block, dict):
                                    continue
                                btype = block.get("type", "")
                                if btype == "text":
                                    text = block.get("text", "")
                                    if text:
                                        lines.append(f"[AGENT] {text}")
                                        lines.append("")
                                elif btype == "tool_use":
                                    tname = block.get("name", "")
                                    tinput = block.get("input", {})
                                    try:
                                        tinput_str = json.dumps(tinput, ensure_ascii=False)
                                    except (TypeError, ValueError):
                                        tinput_str = str(tinput)
                                    if len(tinput_str) > 1500:
                                        tinput_str = tinput_str[:1500] + " ...(truncated)"
                                    lines.append(f"[TOOL] {tname} {tinput_str}")
                                    lines.append("")
                        # Accumulate per-turn token usage as a fallback.
                        usage = message.get("usage", {})
                        message_id = message.get("id")
                        already_counted = isinstance(message_id, str) and message_id in counted_message_ids
                        if isinstance(usage, dict) and not already_counted:
                            if isinstance(message_id, str):
                                counted_message_ids.add(message_id)
                            in_tok += usage.get("input_tokens", 0)
                            in_tok += usage.get("cache_creation_input_tokens", 0)
                            in_tok += usage.get("cache_read_input_tokens", 0)
                            out_tok += usage.get("output_tokens", 0)

                    elif etype == "user":
                        message = event.get("message", {})
                        content = message.get("content", [])
                        if isinstance(content, list):
                            for block in content:
                                if not isinstance(block, dict):
                                    continue
                                if block.get("type") == "tool_result":
                                    result_content = block.get("content", "")
                                    if isinstance(result_content, list):
                                        result_content = "\n".join(
                                            c.get("text", "") if isinstance(c, dict) else str(c) for c in result_content
                                        )
                                    result_content = str(result_content)
                                    if len(result_content) > 3000:
                                        result_content = (
                                            result_content[:1500] + "\n... (truncated) ...\n" + result_content[-1500:]
                                        )
                                    lines.append(f"[TOOL_RESULT] {result_content.rstrip()}")
                                    lines.append("")

                    elif etype == "result":
                        # Final summary — authoritative token totals if present.
                        usage = event.get("usage", {})
                        if isinstance(usage, dict):
                            final_in = (
                                usage.get("input_tokens", 0)
                                + usage.get("cache_creation_input_tokens", 0)
                                + usage.get("cache_read_input_tokens", 0)
                            )
                            final_out = usage.get("output_tokens", 0)
                        subtype = event.get("subtype", "")
                        result_text = event.get("result", "")
                        if result_text:
                            lines.append(f"[RESULT/{subtype}] {result_text}")
                            lines.append("")
                        elif subtype:
                            lines.append(f"[RESULT/{subtype}]")
                            lines.append("")

                    elif etype == "system":
                        # Skip init noise; nothing useful for the transcript.
                        continue
        except FileNotFoundError:
            pass

        # Prefer the final 'result' event totals over per-turn accumulation.
        if final_in is not None and final_out is not None:
            in_tok, out_tok = final_in, final_out

        return "\n".join(lines), in_tok, out_tok

    def parse_usage(self, jsonl_path: str, *, input_tokens: int, output_tokens: int) -> UsageSummary:
        usage = parse_claude_code_usage(jsonl_path, requested_model=self.model)
        if usage is not None:
            return usage
        if input_tokens or output_tokens:
            return UsageSummary(
                input_tokens=nonnegative_int(input_tokens) if input_tokens else None,
                output_tokens=nonnegative_int(output_tokens) if output_tokens else None,
                sources=("claude_code_stream_json",),
                available=True,
                complete=False,
                is_lower_bound=True,
                warnings=("Claude Code usage events unavailable; token usage is incomplete",),
            )
        return UsageSummary(
            sources=("claude_code_stream_json",),
            available=False,
            complete=False,
            warnings=("Claude Code usage events unavailable",),
        )
