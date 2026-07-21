"""OpenAI Codex CLI backend."""

from __future__ import annotations

import json
import math
import os
import re
import subprocess
import tomllib
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

from evaluator import quota
from evaluator.usage import UsageSummary

from .agentic import AgenticBackend
from .base import (
    detect_firewall_hosts,
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "gpt-5.5"

# ChatGPT's hard usage cap surfaces as an `error` / `turn.failed` event whose
# message reads e.g. "You've hit your usage limit. ... try again at 7:24 PM."
_USAGE_LIMIT_RE = re.compile(r"usage limit", re.IGNORECASE)
_RETRY_AT_RE = re.compile(r"try again at\s+(\d{1,2}):(\d{2})\s*([AaPp][Mm])")

# detect_quota_block runs host-side (after the agent container exits) where the
# repo and ~/.codex are available, so it can reuse the usage probe's precise reset.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
_CODEX_USAGE_SOURCE = "codex_cli_turn_completed"
_MODEL_ACTIVITY_ITEM_TYPES = frozenset(
    {
        "agent_message",
        "reasoning",
        "command_execution",
        "file_change",
        "mcp_tool_call",
        "collab_tool_call",
        "web_search",
        "todo_list",
    }
)
_STREAM_LAG_RE = re.compile(r"event stream lagged; dropped\s+\d+\s+events?", re.IGNORECASE)


@dataclass(frozen=True)
class _CodexTerminalUsage:
    input_tokens: int
    output_tokens: int
    cache_read_input_tokens: int | None
    reasoning_output_tokens: int | None
    incomplete: bool
    warnings: tuple[str, ...]


@dataclass(frozen=True)
class _ParsedCodexRun:
    transcript: str
    usage: UsageSummary


def _strict_token(value: object) -> int | None:
    """Validate a native Codex token field without coercion."""

    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else None


def _parse_terminal_usage(event: dict[str, Any]) -> tuple[_CodexTerminalUsage | None, tuple[str, ...]]:
    raw_usage = event.get("usage")
    if not isinstance(raw_usage, dict):
        return None, ("Codex turn.completed event has no usage object",)

    input_tokens = _strict_token(raw_usage.get("input_tokens"))
    output_tokens = _strict_token(raw_usage.get("output_tokens"))
    core_errors = []
    if input_tokens is None:
        core_errors.append("input_tokens")
    if output_tokens is None:
        core_errors.append("output_tokens")
    if core_errors:
        return None, (f"Codex turn.completed has invalid core fields: {', '.join(core_errors)}",)

    if input_tokens == 0 and output_tokens == 0:
        # Codex's JSONL event processor uses Usage::default() when it never
        # received a native token update, so this shape is not proof of a free run.
        return None, ("Codex reported synthesized-looking all-zero terminal usage",)

    warnings: list[str] = []
    incomplete = False

    def optional_subset(name: str) -> int | None:
        nonlocal incomplete
        if name not in raw_usage:
            warnings.append(f"Codex turn.completed is missing {name}")
            incomplete = True
            return None
        value = _strict_token(raw_usage[name])
        if value is None:
            warnings.append(f"Codex turn.completed has invalid {name}")
            incomplete = True
        return value

    cached_input_tokens = optional_subset("cached_input_tokens")
    reasoning_output_tokens = optional_subset("reasoning_output_tokens")
    if cached_input_tokens is not None and cached_input_tokens > input_tokens:
        warnings.append("Codex cached input tokens exceed total input tokens")
        cached_input_tokens = None
        incomplete = True
    if reasoning_output_tokens is not None and reasoning_output_tokens > output_tokens:
        warnings.append("Codex reasoning output tokens exceed total output tokens")
        reasoning_output_tokens = None
        incomplete = True

    return (
        _CodexTerminalUsage(
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cache_read_input_tokens=cached_input_tokens,
            reasoning_output_tokens=reasoning_output_tokens,
            incomplete=incomplete,
            warnings=tuple(warnings),
        ),
        (),
    )


def _append_transcript_event(lines: list[str], event: dict[str, Any]) -> None:
    etype = event.get("type")
    if etype == "item.completed":
        item = event.get("item")
        if not isinstance(item, dict):
            return
        itype = item.get("type")
        if itype == "agent_message":
            text = item.get("text")
            if isinstance(text, str) and text:
                lines.extend((f"[AGENT] {text}", ""))
        elif itype == "command_execution":
            command = item.get("command", "")
            output = item.get("aggregated_output", "")
            lines.append(f"[CMD] {command}")
            if output:
                output = str(output)
                if len(output) > 3000:
                    output = output[:1500] + "\n... (truncated) ...\n" + output[-1500:]
                lines.append(output.rstrip())
            if item.get("exit_code") is not None:
                lines.append(f"[EXIT {item['exit_code']}]")
            lines.append("")
        elif itype == "file_change":
            changes = item.get("changes")
            if isinstance(changes, list):
                paths = [change.get("path") for change in changes if isinstance(change, dict)]
                lines.extend((f"[EDIT] {', '.join(path for path in paths if isinstance(path, str))}", ""))
        elif itype == "error":
            lines.extend((f"[WARNING] {item.get('message', '')}", ""))
    elif etype == "error":
        lines.extend((f"[ERROR] {event.get('message', '')}", ""))


def _retry_may_duplicate_model_work(jsonl_path: str) -> bool:
    """Detect native activity or a stream too incomplete to retry safely."""

    saw_turn_started = False
    saw_turn_failed = False
    failure_messages: list[str] = []
    try:
        with open(jsonl_path) as f:
            for raw in f:
                if not raw.strip():
                    continue
                try:
                    event = json.loads(raw)
                except (json.JSONDecodeError, TypeError):
                    return True
                if not isinstance(event, dict):
                    return True
                event_type = event.get("type")
                if not isinstance(event_type, str):
                    return True
                if event_type == "turn.started":
                    saw_turn_started = True
                elif event_type == "turn.completed":
                    return True
                elif event_type == "turn.failed":
                    saw_turn_failed = True
                    error = event.get("error")
                    message = error.get("message") if isinstance(error, dict) else None
                    if isinstance(message, str):
                        failure_messages.append(message)
                elif event_type == "error":
                    message = event.get("message")
                    if isinstance(message, str):
                        failure_messages.append(message)
                item = event.get("item")
                if not event_type.startswith("item.") or not isinstance(item, dict):
                    continue
                item_type = item.get("type")
                if isinstance(item_type, str) and item_type in _MODEL_ACTIVITY_ITEM_TYPES:
                    return True
                if item_type == "error":
                    message = item.get("message")
                    if isinstance(message, str) and _STREAM_LAG_RE.search(message):
                        # This warning is not itself model work, but events that
                        # would prove work may be among those dropped. Retrying
                        # such a launch could silently duplicate paid work.
                        return True
    except FileNotFoundError:
        return False
    except (OSError, UnicodeError):
        return True

    if saw_turn_failed and not saw_turn_started:
        # A terminal failure without its required start event is a damaged
        # lifecycle, so it cannot prove that dispatch never happened.
        return True
    if not saw_turn_started:
        return False
    # The explicit provider cap is a rejection, not an interrupted generation.
    # It owns a separate wait-and-retry path in the runner. Every other started
    # failure may have reached the provider before its first item event arrived.
    return not (
        saw_turn_failed and failure_messages and all(_USAGE_LIMIT_RE.search(message) for message in failure_messages)
    )


def _parse_codex_run(jsonl_path: str) -> _ParsedCodexRun:
    lines: list[str] = []
    terminal_events: list[dict[str, Any]] = []
    terminal_usages: list[_CodexTerminalUsage] = []
    warnings: list[str] = []
    malformed_lines = 0
    failed_turns = 0
    saw_multi_agent_activity = False
    saw_stream_lag = False

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
                _append_transcript_event(lines, event)
                event_type = event.get("type")
                item = event.get("item")
                if isinstance(event_type, str) and event_type.startswith("item.") and isinstance(item, dict):
                    item_type = item.get("type")
                    if item_type == "collab_tool_call":
                        saw_multi_agent_activity = True
                    elif item_type == "error":
                        message = item.get("message")
                        if isinstance(message, str) and _STREAM_LAG_RE.search(message):
                            saw_stream_lag = True
                if event_type == "turn.completed":
                    terminal_events.append(event)
                    terminal_usage, terminal_warnings = _parse_terminal_usage(event)
                    warnings.extend(terminal_warnings)
                    if terminal_usage is not None:
                        terminal_usages.append(terminal_usage)
                elif event_type == "turn.failed":
                    failed_turns += 1
    except (OSError, UnicodeError) as exc:
        return _ParsedCodexRun(
            transcript="\n".join(lines),
            usage=UsageSummary(
                sources=("codex_cli_jsonl",),
                available=False,
                warnings=(f"Codex JSONL output unavailable: {type(exc).__name__}",),
            ),
        )

    if malformed_lines:
        warnings.append(f"Codex JSONL contains {malformed_lines} malformed nonempty line(s)")
    if saw_stream_lag:
        warnings.append("Codex reported dropped JSONL events; model activity and usage may be incomplete")
    if not terminal_usages:
        if not terminal_events:
            warnings.append("Codex turn.completed usage is unavailable")
        if failed_turns:
            warnings.append("Codex turn failed before terminal usage was emitted")
        return _ParsedCodexRun(
            transcript="\n".join(lines),
            usage=UsageSummary(
                sources=("codex_cli_jsonl",),
                available=False,
                warnings=tuple(dict.fromkeys(warnings)),
            ),
        )

    selected = terminal_usages[-1]
    warnings.extend(selected.warnings)
    lower_bound = False
    if len(terminal_events) > 1:
        warnings.append("Codex JSONL contains multiple turn.completed events; using the last usable aggregate")
        lower_bound = True
    if malformed_lines:
        lower_bound = True
    if failed_turns:
        warnings.append("Codex JSONL contains both failed and completed turn events")
        lower_bound = True
    if saw_multi_agent_activity:
        warnings.append(
            "Codex JSONL contains multi-agent activity; the terminal aggregate covers only the parent thread"
        )
        lower_bound = True
    if saw_stream_lag:
        lower_bound = True

    return _ParsedCodexRun(
        transcript="\n".join(lines),
        usage=UsageSummary(
            input_tokens=selected.input_tokens,
            output_tokens=selected.output_tokens,
            cache_read_input_tokens=selected.cache_read_input_tokens,
            cache_write_input_tokens=None,
            reasoning_output_tokens=selected.reasoning_output_tokens,
            model_requests=None,
            model_time_secs=None,
            costs=(),
            requests=(),
            sources=(_CODEX_USAGE_SOURCE,),
            available=True,
            complete=not lower_bound and not selected.incomplete,
            is_lower_bound=lower_bound,
            warnings=tuple(dict.fromkeys(warnings)),
        ),
    )


class CodexBackend(AgenticBackend):
    name = "codex"
    install_script = "install-codex.sh"
    session_state_dir = "/root/.codex"
    env_keys = [
        "OPENAI_API_KEY",
        "AZURE_OPENAI_API_KEY",
        "AZURE_OPENAI_HOST",
        "AWS_BEARER_TOKEN_BEDROCK",
        "AWS_REGION",
        "AWS_DEFAULT_REGION",
        "AWS_PROFILE",
    ]
    credential_mounts = ["codex"]
    reasoning_effort_values = ("none", "minimal", "low", "medium", "high", "xhigh", "max", "ultra")

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        last_msg_path = os.path.join(result_dir, "codex_last_message.txt")
        # Invoke the `codex` binary directly (it must be on PATH). Going through
        # `npx codex` is wrong: npm has no top-level `codex` package (OpenAI's is
        # `@openai/codex`), so `npx codex` resolves to an unrelated bogus package.
        cmd = [
            "codex",
            "exec",
            "--dangerously-bypass-approvals-and-sandbox",
            "-C",
            workspace,
            "-m",
            self.model,
            "-c",
            "web_search=disabled",
            # codex exec reports usage for its primary thread only. Disable every
            # native child-agent entry point so a clean terminal aggregate is an
            # exact total for the whole benchmark invocation.
            "-c",
            "features.multi_agent=false",
            "-c",
            "features.multi_agent_v2=false",
            "-c",
            "features.enable_fanout=false",
            "--json",
            "-o",
            last_msg_path,
        ]
        if self.reasoning_effort is not None:
            cmd.extend(["-c", f"model_reasoning_effort={self.reasoning_effort}"])
        if self._uses_bedrock():
            cmd.extend(["-c", 'model_provider="amazon-bedrock"'])
        return cmd

    def get_credential_mounts(self) -> list[str]:
        mounts = []
        if self._uses_bedrock() or not self._has_api_key_auth():
            mounts.append("codex")
        if self._uses_bedrock() and needs_aws_shared_credentials():
            mounts.append("aws")
        return mounts

    @staticmethod
    def _has_api_key_auth() -> bool:
        return bool(os.environ.get("OPENAI_API_KEY") or os.environ.get("AZURE_OPENAI_API_KEY"))

    def _uses_bedrock(self) -> bool:
        if self.model.startswith("openai."):
            return True
        return self._host_config_uses_bedrock()

    @staticmethod
    def _host_config_uses_bedrock() -> bool:
        config_path = Path.home() / ".codex" / "config.toml"
        try:
            with open(config_path, "rb") as f:
                config = tomllib.load(f)
        except (FileNotFoundError, OSError, tomllib.TOMLDecodeError):
            return False
        return config.get("model_provider") == "amazon-bedrock"

    @staticmethod
    def _host_config_has_bedrock_region() -> bool:
        config_path = Path.home() / ".codex" / "config.toml"
        try:
            with open(config_path, "rb") as f:
                config = tomllib.load(f)
        except (FileNotFoundError, OSError, tomllib.TOMLDecodeError):
            return False
        provider = config.get("model_providers", {}).get("amazon-bedrock", {})
        aws = provider.get("aws", {}) if isinstance(provider, dict) else {}
        region = aws.get("region") if isinstance(aws, dict) else None
        return isinstance(region, str) and bool(region)

    def check_auth(self) -> str | None:
        if self._uses_bedrock():
            if has_aws_bedrock_bearer_token():
                if not (has_aws_region() or self._host_config_has_bedrock_region()):
                    return "codex: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock bearer-token auth"
                return None
            if has_aws_env_credentials():
                if not (has_aws_region() or self._host_config_has_bedrock_region()):
                    return "codex: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock AWS env auth"
                return None
            if has_aws_shared_credentials():
                return None
            return "codex: Bedrock selected but no AWS credentials detected"
        # Fast paths: an env var is set (direct OpenAI or Azure routing).
        if os.environ.get("OPENAI_API_KEY") or os.environ.get("AZURE_OPENAI_API_KEY"):
            return None
        # Slow path: ask codex itself whether it's logged in (OAuth/ChatGPT).
        # This is a local read of ~/.codex state, no API call, no session.
        try:
            r = subprocess.run(
                ["codex", "login", "status"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if r.returncode == 0 and "Logged in" in (r.stdout + r.stderr):
                return None
        except FileNotFoundError:
            return "codex: `codex` CLI not found on PATH"
        except Exception:
            pass
        return "codex: no auth detected. Set OPENAI_API_KEY or AZURE_OPENAI_API_KEY, or run `codex login`."

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def usage_script(self) -> str | None:
        return "scripts/usage/codex.sh"

    def default_quota(self) -> tuple[float, float]:
        return (95.0, 95.0)

    def detect_quota_block(self, jsonl_path: str) -> int | None:
        """Detect ChatGPT's hard 'usage limit' cap and return seconds to wait.

        The percentage gate cannot see this: once capped, codex's turns fail
        instantly with no `usage` event, so the rolling utilization the gate reads
        goes stale/low and never trips — every subsequent task fails in ~3s and is
        misgraded as FAIL. We scan the run's own events for the explicit usage-limit
        error and sleep until the stated reset instead. Returns None if no cap.
        """
        msg = None
        saw_completed_turn = False
        try:
            with open(jsonl_path) as f:
                for raw in f:
                    raw = raw.strip()
                    if not raw:
                        continue
                    try:
                        ev = json.loads(raw)
                    except json.JSONDecodeError:
                        continue
                    if not isinstance(ev, dict):
                        continue
                    t = ev.get("type", "")
                    if t == "turn.completed":
                        saw_completed_turn = True
                        continue
                    if t == "error":
                        candidate = ev.get("message")
                        m = candidate if isinstance(candidate, str) else ""
                    elif t == "turn.failed":
                        error = ev.get("error")
                        candidate = error.get("message") if isinstance(error, dict) else None
                        m = candidate if isinstance(candidate, str) else ""
                    else:
                        continue
                    if m and _USAGE_LIMIT_RE.search(m):
                        msg = m  # keep the last occurrence
        except (OSError, UnicodeError):
            return None
        if msg is None or saw_completed_turn:
            return None
        # Prefer the precise reset epoch codex records in its session rollout (what
        # the usage probe reads) over parsing the human "try again at 7:24 PM"
        # string, which is timezone- and boundary-fragile. Fall back to the prose
        # time only when the probe has no data.
        reset_at = self._reset_at_from_probe()
        when = reset_at if reset_at is not None else self._parse_retry_time(msg)
        return quota.secs_until_reset(when, clamp_hi=6 * 3600, fallback=1800)

    def _reset_at_from_probe(self) -> str | None:
        """The reset time (ISO) of the window that hit its cap, from the codex
        usage probe — or None.

        Codex records a structured ``resets_at`` epoch per window in its session
        rollout, far more reliable than the human time in the cap message. The
        binding window is the one at its cap (utilization >= 100); when both the 5h
        and weekly windows are capped we wait for the later reset, so a weekly cap
        with a fresh 5h window doesn't make us retry-thrash until the 5h resets.
        Falls back to the most-utilized window, then to None (prose time) when the
        probe can't be read (no repo script, no ~/.codex, API-key auth).
        """
        rel = self.usage_script()
        if not rel:
            return None
        usage = quota.fetch_usage(os.path.join(_REPO_ROOT, rel))
        if not usage:
            return None
        raw_windows = (usage.get("five_hour"), usage.get("seven_day"))
        windows = [window for window in raw_windows if isinstance(window, dict)]

        def utilization(window: dict[str, object]) -> int | float:
            value = window.get("utilization")
            if isinstance(value, int) and not isinstance(value, bool):
                return value if value >= 0 else 0
            if isinstance(value, float) and value >= 0 and math.isfinite(value):
                return value
            return 0

        def has_reset(window: dict[str, object]) -> bool:
            value = window.get("resets_at")
            return isinstance(value, str) and bool(value)

        capped = [window for window in windows if utilization(window) >= 100 and has_reset(window)]
        if capped:
            return max(str(window["resets_at"]) for window in capped)  # wait past the last-clearing cap
        with_reset = [window for window in windows if has_reset(window)]
        if not with_reset:
            return None
        return str(max(with_reset, key=utilization)["resets_at"])

    @staticmethod
    def _parse_retry_time(msg: str) -> datetime | None:
        """Parse 'try again at 7:24 PM' from a usage-limit message into a datetime
        (today, or tomorrow if that time already passed), or None if absent. Waking
        too early (timezone skew) is self-correcting: the retry re-hits the cap and
        re-sleeps on the fresh error.
        """
        m = _RETRY_AT_RE.search(msg)
        if not m:
            return None
        try:
            hh, mm, ap = int(m.group(1)), int(m.group(2)), m.group(3).upper()
            if ap == "PM" and hh != 12:
                hh += 12
            elif ap == "AM" and hh == 12:
                hh = 0
            now = datetime.now()
            target = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
            if target <= now:
                target += timedelta(days=1)
            return target
        except Exception:
            return None

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        parsed = _parse_codex_run(jsonl_path)
        return parsed.transcript, parsed.usage.legacy_input_tokens, parsed.usage.legacy_output_tokens

    def parse_usage(self, jsonl_path: str, *, input_tokens: int, output_tokens: int) -> UsageSummary:
        # The legacy counts are produced by this same parser. Read the native
        # terminal aggregate again so structured and compatibility fields share
        # one protocol interpretation and can never double-count intermediates.
        del input_tokens, output_tokens
        return _parse_codex_run(jsonl_path).usage

    def retry_may_duplicate_model_work(self, jsonl_path: str) -> bool:
        # A failed turn has no native token aggregate. Known model-driven item
        # types prove activity; a stream-lag warning means such proof may have
        # been dropped. Both make an automatic replacement unsafe without
        # fabricating request or token counts.
        return _retry_may_duplicate_model_work(jsonl_path)

    def attempt_output_files(self) -> tuple[str, ...]:
        # `-o` is only written after a final response. Without isolating it, a
        # later failed retry can leave an earlier launch's message looking final.
        return ("codex_last_message.txt",)
