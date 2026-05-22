"""OpenAI Codex CLI backend."""

from __future__ import annotations

import json
import os
from typing import Tuple

from .base import AgentBackend


class CodexBackend(AgentBackend):
    name = "codex"

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        last_msg_path = os.path.join(result_dir, "codex_last_message.txt")
        return [
            "npx", "codex", "exec",
            "--dangerously-bypass-approvals-and-sandbox",
            "-C", workspace,
            "-m", "gpt55",
            "--json",
            "-o", last_msg_path,
        ]

    def required_env(self) -> list[str]:
        return ["OPENAI_API_KEY"]

    def firewall_hosts(self) -> list[str]:
        return ["api.openai.com"]

    def parse_output(self, jsonl_path: str) -> Tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0

        try:
            with open(jsonl_path, "r") as f:
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
