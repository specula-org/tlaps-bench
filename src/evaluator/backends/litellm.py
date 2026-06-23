"""LiteLLM backend — evaluate any model via unified API."""

from __future__ import annotations

import json
import os
import sys

import litellm

from .base import AgentBackend

DEFAULT_MODEL = "gpt-5.5"


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
        "AWS_REGION_NAME",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        return [
            "python3",
            "-m",
            "evaluator.backends.litellm_agent",
            "--workspace",
            workspace,
            "--model",
            self.model,
        ]

    def firewall_hosts(self) -> list[str]:
        m = self.model.lower()
        if "anthropic" in m or "claude" in m:
            return ["api.anthropic.com"]
        if "gemini" in m or "google" in m:
            return ["generativelanguage.googleapis.com"]
        if "deepseek" in m:
            return ["api.deepseek.com"]
        return ["api.openai.com"]

    def check_auth(self) -> str | None:
        m = self.model.lower()
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


def run_preflight() -> None:
    """Validate model + credentials by making a minimal LiteLLM API call."""
    m = os.environ.get("AGENT_MODEL_ID", "gpt-5.5")
    try:
        response = litellm.completion(
            model=m,
            messages=[{"role": "user", "content": "say ok"}],
            max_tokens=5,
        )
        if not response.choices[0].message.content:
            print("empty response from model")
            sys.exit(1)
    except Exception as e:
        print(f"preflight failed: {e}")
        sys.exit(1)
