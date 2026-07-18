"""LiteLLM backend — evaluate any model via unified API."""

from __future__ import annotations

import json

from .agentic import AgenticBackend
from .base import detect_firewall_hosts
from .litellm_common import DEFAULT_MODEL, ENV_KEYS, check_auth, credential_mounts, uses_bedrock


class LiteLLMBackend(AgenticBackend):
    name = "litellm"
    install_script = "install-litellm.sh"
    env_keys = ENV_KEYS

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        return credential_mounts(self.model)

    def _uses_bedrock(self) -> bool:
        return uses_bedrock(self.model)

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
