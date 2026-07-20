"""Pi coding agent backend."""

from __future__ import annotations

import json
import os
import shlex
from pathlib import Path

from .agentic import AgenticBackend
from .base import (
    detect_firewall_hosts,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
)

DEFAULT_MODEL = "openai/gpt-5.5"


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

                    if event.get("type") == "message_update":
                        update = event.get("assistantMessageEvent") or {}
                        if update.get("type") == "text_delta" and update.get("delta"):
                            lines.append(update["delta"])
                    elif event.get("type") == "message_end":
                        message = event.get("message") or {}
                        usage = message.get("usage") or {}
                        in_tok += usage.get("input", 0) or 0
                        out_tok += usage.get("output", 0) or 0
                        in_tok += usage.get("cacheRead", 0) or 0
        except FileNotFoundError:
            pass

        return "".join(lines), in_tok, out_tok

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
