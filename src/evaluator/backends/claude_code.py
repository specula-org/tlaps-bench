"""Anthropic Claude Code CLI backend."""

from __future__ import annotations

import json
import os
import subprocess

from .base import (
    AgentBackend,
    detect_firewall_hosts,
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_region,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "claude-opus-4-7"


class ClaudeCodeBackend(AgentBackend):
    name = "claude_code"
    install_script = "install-claudecode.sh"
    env_keys = [
        "ANTHROPIC_API_KEY",
        "CLAUDE_CODE_USE_BEDROCK",
        "CLAUDE_CODE_USE_MANTLE",
        "AWS_BEARER_TOKEN_BEDROCK",
        "AWS_REGION",
        "AWS_DEFAULT_REGION",
        "AWS_PROFILE",
        "ANTHROPIC_BEDROCK_BASE_URL",
        "ANTHROPIC_AWS_BASE_URL",
        "ANTHROPIC_SMALL_FAST_MODEL_AWS_REGION",
        "DISABLE_PROMPT_CACHING",
    ]

    # Tools the agent is allowed to use (mirrors SREGym's whitelist).
    # Using --allowedTools instead of --dangerously-skip-permissions
    # because the latter is blocked when running as root in containers.
    ALLOWED_TOOLS = [
        "Bash",
        "Edit",
        "Write",
        "Read",
        "Glob",
        "Grep",
        "LS",
        "NotebookEdit",
        "NotebookRead",
        "TodoRead",
        "TodoWrite",
        "Agent",
        "Skill",
        "SlashCommand",
        "Task",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        if self._uses_aws_provider() and needs_aws_shared_credentials():
            return ["aws"]
        if not self._uses_aws_provider() and self._needs_claude_credentials():
            return ["claude"]
        return []

    @staticmethod
    def _uses_aws_provider() -> bool:
        return (
            os.environ.get("CLAUDE_CODE_USE_BEDROCK", "").strip() == "1"
            or os.environ.get("CLAUDE_CODE_USE_MANTLE", "").strip() == "1"
        )

    @staticmethod
    def _needs_claude_credentials() -> bool:
        return not (os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"))

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        return [
            "claude",
            "--print",
            "--no-session-persistence",
            "--output-format",
            "stream-json",
            "--verbose",
            "--effort",
            "max",
            "--model",
            self.model,
            "--allowedTools",
        ] + self.ALLOWED_TOOLS

    def check_auth(self) -> str | None:
        if self._uses_aws_provider():
            if has_aws_bedrock_bearer_token():
                if not has_aws_region():
                    return "claude_code: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock bearer-token auth"
                return None
            if has_aws_env_credentials():
                if not has_aws_region():
                    return "claude_code: AWS_REGION or AWS_DEFAULT_REGION required for Bedrock AWS env auth"
                return None
            if has_aws_shared_credentials():
                return None
            return "claude_code: Bedrock/Mantle selected but no AWS credentials detected"
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
        return detect_firewall_hosts(self.model)

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
