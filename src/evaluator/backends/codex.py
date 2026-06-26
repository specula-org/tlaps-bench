"""OpenAI Codex CLI backend."""

from __future__ import annotations

import json
import os
import subprocess
import tomllib
from pathlib import Path

from .base import (
    AgentBackend,
    detect_firewall_hosts,
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "gpt-5.5"


class CodexBackend(AgentBackend):
    name = "codex"
    install_script = "install-codex.sh"
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
