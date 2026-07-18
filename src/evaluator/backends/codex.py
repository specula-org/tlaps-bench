"""OpenAI Codex CLI backend."""

from __future__ import annotations

import json
import os
import re
import subprocess
import tomllib
from datetime import datetime, timedelta
from pathlib import Path

from evaluator import quota

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
    supports_reasoning_effort = True

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
                    t = ev.get("type", "")
                    if t == "error":
                        m = ev.get("message", "")
                    elif t == "turn.failed":
                        m = (ev.get("error") or {}).get("message", "")
                    else:
                        continue
                    if m and _USAGE_LIMIT_RE.search(m):
                        msg = m  # keep the last occurrence
        except FileNotFoundError:
            return None
        if msg is None:
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
        windows = [usage.get("five_hour") or {}, usage.get("seven_day") or {}]
        capped = [w for w in windows if (w.get("utilization") or 0) >= 100 and w.get("resets_at")]
        if capped:
            return max(w["resets_at"] for w in capped)  # wait past the last-clearing cap
        with_reset = [w for w in windows if w.get("resets_at")]
        if not with_reset:
            return None
        return max(with_reset, key=lambda w: w.get("utilization") or 0)["resets_at"]

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

                    if etype == "item.completed":
                        item = event.get("item", {})
                        itype = item.get("type", "")
                        if itype == "agent_message":
                            text = item.get("text", "")
                            if text:
                                lines.append(f"[AGENT] {text}")
                                lines.append("")
                        elif itype == "command_execution":
                            cmd = item.get("command", "")
                            output = item.get("aggregated_output", "")
                            exit_code = item.get("exit_code", "")
                            lines.append(f"[CMD] {cmd}")
                            if output:
                                if len(output) > 3000:
                                    output = output[:1500] + "\n... (truncated) ...\n" + output[-1500:]
                                lines.append(output.rstrip())
                            if exit_code is not None:
                                lines.append(f"[EXIT {exit_code}]")
                            lines.append("")
                        elif itype == "file_edit":
                            lines.append(f"[EDIT] {item.get('filepath', '')}")
                            lines.append("")
                    elif etype == "error":
                        lines.append(f"[ERROR] {event.get('message', '')}")
                        lines.append("")

                    if "usage" in event:
                        u = event["usage"]
                        in_tok += u.get("input_tokens", 0)
                        out_tok += u.get("output_tokens", 0)
        except FileNotFoundError:
            pass

        return "\n".join(lines), in_tok, out_tok
