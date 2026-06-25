"""LiteLLM backend — evaluate any model via unified API."""

from __future__ import annotations

import json
import os

from .base import (
    AgentBackend,
    detect_firewall_hosts,
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "claude-sonnet-4-6"


class LiteLLMBackend(AgentBackend):
    name = "litellm"
    install_script = "install-litellm.sh"
    env_keys = [
        "OPENAI_API_KEY",
        "ANTHROPIC_API_KEY",
        "GOOGLE_API_KEY",
        "GEMINI_API_KEY",
        "AZURE_OPENAI_API_KEY",
        "AZURE_API_BASE",
        "AZURE_API_VERSION",
        "DEEPSEEK_API_KEY",
        "AWS_ACCESS_KEY_ID",
        "AWS_SECRET_ACCESS_KEY",
        "AWS_REGION",
        "AWS_DEFAULT_REGION",
        "AWS_REGION_NAME",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        if self._uses_bedrock() and needs_aws_shared_credentials():
            return ["aws"]
        return []

    def _uses_bedrock(self) -> bool:
        return "bedrock" in self.model.lower()

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        return [
            "python3",
            "/opt/litellm_agent.py",
            "--workspace",
            workspace,
            "--model",
            self.model,
        ]

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def check_auth(self) -> str | None:
        m = self.model.lower()
        if "bedrock" in m:
            if has_aws_bedrock_bearer_token():
                if not (os.environ.get("AWS_REGION_NAME") or os.environ.get("AWS_REGION")):
                    return "litellm: AWS_REGION_NAME or AWS_REGION required for bedrock bearer-token auth"
                return None
            if has_aws_env_credentials():
                if not (os.environ.get("AWS_REGION_NAME") or os.environ.get("AWS_REGION")):
                    return "litellm: AWS_REGION_NAME or AWS_REGION required for bedrock model"
                return None
            if has_aws_shared_credentials():
                return None
            return "litellm: AWS credentials not found for bedrock model"
        if "anthropic" in m or "claude" in m:
            if os.environ.get("ANTHROPIC_API_KEY"):
                return None
            return "litellm: ANTHROPIC_API_KEY not set for anthropic model"
        if "gemini" in m or "google" in m:
            if os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY"):
                return None
            return "litellm: GOOGLE_API_KEY or GEMINI_API_KEY not set for google model"
        if "deepseek" in m:
            if os.environ.get("DEEPSEEK_API_KEY"):
                return None
            return "litellm: DEEPSEEK_API_KEY not set for deepseek model"
        if os.environ.get("OPENAI_API_KEY") or os.environ.get("AZURE_OPENAI_API_KEY"):
            return None
        return "litellm: OPENAI_API_KEY not set"

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
