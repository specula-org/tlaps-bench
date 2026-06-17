"""OpenAI Codex CLI backend."""

from __future__ import annotations

import json
import os
import subprocess

from .base import AgentBackend

DEFAULT_MODEL = "gpt-5.5"


class CodexBackend(AgentBackend):
    name = "codex"

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        last_msg_path = os.path.join(result_dir, "codex_last_message.txt")
        return [
            "npx",
            "codex",
            "exec",
            "--dangerously-bypass-approvals-and-sandbox",
            "-C",
            workspace,
            "-m",
            self.model,
            "--json",
            "-o",
            last_msg_path,
        ]

    def check_auth(self) -> str | None:
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
        return ["api.openai.com"]

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
