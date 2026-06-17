"""Anthropic Claude Code CLI backend."""

from __future__ import annotations

import json
import os
import subprocess

from .base import AgentBackend

DEFAULT_MODEL = "claude-opus-4-7"


class ClaudeCodeBackend(AgentBackend):
    name = "claude_code"

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        # claude has no -C / --cwd flag; runner sets cwd=workspace.
        # stream-json requires --verbose in non-interactive (--print) mode.
        # --no-session-persistence keeps benchmark runs out of the user's
        # /resume history (193 entries per full run otherwise).
        # --effort max runs the highest reasoning budget (levels:
        # low|medium|high|xhigh|max) so the comparison against Codex's
        # xhigh reasoning is apples-to-apples; without it the CLI uses a
        # lighter default.
        return [
            "claude",
            "--print",
            "--dangerously-skip-permissions",
            "--no-session-persistence",
            "--output-format",
            "stream-json",
            "--verbose",
            "--effort",
            "max",
            "--model",
            self.model,
        ]

    def check_auth(self) -> str | None:
        # Fast path: env var present.
        if os.environ.get("ANTHROPIC_API_KEY"):
            return None
        # Slow path: probe the CLI with --no-session-persistence so the
        # probe doesn't pollute the user's resume history. This makes one
        # tiny API call but covers OAuth / subscription auth that env-var
        # checks can't see.
        try:
            r = subprocess.run(
                ["claude", "--print", "--no-session-persistence", "--output-format", "text", "ok"],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if r.returncode == 0:
                return None
            stderr = (r.stderr or r.stdout or "").strip()
            if len(stderr) > 300:
                stderr = stderr[:300] + "..."
            return f"claude_code: auth probe failed (exit {r.returncode}): {stderr}"
        except subprocess.TimeoutExpired:
            return "claude_code: auth probe timed out (>30s)"
        except FileNotFoundError:
            return "claude_code: `claude` CLI not found on PATH"
        except Exception as e:
            return f"claude_code: auth probe error: {e}"

    def firewall_hosts(self) -> list[str]:
        return ["api.anthropic.com"]

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0
        final_in = None
        final_out = None

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
                                            c.get("text", "") if isinstance(c, dict) else str(c) for c in result_content
                                        )
                                    result_content = str(result_content)
                                    if len(result_content) > 3000:
                                        result_content = (
                                            result_content[:1500] + "\n... (truncated) ...\n" + result_content[-1500:]
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
