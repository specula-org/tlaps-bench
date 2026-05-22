"""Anthropic Claude Code CLI backend."""

from __future__ import annotations

import json
from typing import Tuple

from .base import AgentBackend


DEFAULT_MODEL = "claude-opus-4-7"


class ClaudeCodeBackend(AgentBackend):
    name = "claude_code"

    def __init__(self, model: str = DEFAULT_MODEL):
        self.model = model

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        # claude has no -C / --cwd flag; runner sets cwd=workspace.
        # stream-json requires --verbose in non-interactive (--print) mode.
        return [
            "claude",
            "--print",
            "--dangerously-skip-permissions",
            "--output-format", "stream-json",
            "--verbose",
            "--model", self.model,
        ]

    def required_env(self) -> list[str]:
        return ["ANTHROPIC_API_KEY"]

    def firewall_hosts(self) -> list[str]:
        return ["api.anthropic.com"]

    def parse_output(self, jsonl_path: str) -> Tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0
        final_in = None
        final_out = None

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
                        if isinstance(usage, dict):
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
                                            c.get("text", "") if isinstance(c, dict) else str(c)
                                            for c in result_content
                                        )
                                    result_content = str(result_content)
                                    if len(result_content) > 3000:
                                        result_content = (
                                            result_content[:1500]
                                            + "\n... (truncated) ...\n"
                                            + result_content[-1500:]
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
