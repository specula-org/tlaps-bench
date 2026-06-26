"""GitHub Copilot CLI backend."""

from __future__ import annotations

import json
import os
import subprocess

from .base import AgentBackend, detect_firewall_hosts

DEFAULT_MODEL = "claude-opus-4.8"


class CopilotBackend(AgentBackend):
    name = "copilot"
    install_script = "install-copilot.sh"
    env_keys = [
        "COPILOT_GITHUB_TOKEN",
        "GH_TOKEN",
        "GITHUB_TOKEN",
        "COPILOT_PROVIDER_BASE_URL",
        "COPILOT_PROVIDER_API_KEY",
        "COPILOT_PROVIDER_TYPE",
        "COPILOT_MODEL",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        # Prompt is fed via stdin (the runner pipes it in). copilot's -p flag
        # requires the text as an argument, but with no -p it reads the prompt
        # from stdin and runs non-interactively, exiting when done.
        # --allow-all is required for non-interactive tool use (no approvals).
        # --output-format json emits JSONL (one event per line) to stdout.
        # --disable-builtin-mcps drops the GitHub MCP server: it needs no
        # network beyond the model API and prevents data leakage from
        # github.com lookups (matching the firewalled codex/claude runs).
        # --no-custom-instructions keeps runs reproducible across machines.
        # --no-auto-update stops the CLI from hitting api.github.com for a
        # release check, so the *only* host it needs is the Copilot
        # inference API (no GitHub repo/web access — anti-cheating parity
        # with the firewalled codex/claude runs).
        # --effort max mirrors the highest reasoning budget used for the
        # other backends so the comparison is apples-to-apples.
        return [
            "copilot",
            "--allow-all",
            "-C",
            workspace,
            "--output-format",
            "json",
            "--model",
            self.model,
            "--effort",
            "max",
            "--log-level",
            "none",
            "--no-color",
            "--disable-builtin-mcps",
            "--no-custom-instructions",
            "--no-auto-update",
            "--excluded-tools",
            "web_fetch",
        ]

    def check_auth(self) -> str | None:
        # BYOK mode: provider env vars are set
        if os.environ.get("COPILOT_PROVIDER_BASE_URL"):
            return None
        # Fast path: a token env var is set (headless auth).
        if os.environ.get("COPILOT_GITHUB_TOKEN") or os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN"):
            return None
        # Slow path: probe the CLI with a trivial prompt. This covers OAuth
        # (`copilot login`) / credential-store auth that env-var checks can't
        # see. --disable-builtin-mcps keeps the probe fast and offline-safe.
        try:
            r = subprocess.run(
                [
                    "copilot",
                    "--allow-all",
                    "--disable-builtin-mcps",
                    "--no-color",
                    "--no-auto-update",
                    "--output-format",
                    "text",
                    "-p",
                    "ok",
                ],
                capture_output=True,
                text=True,
                timeout=60,
            )
            if r.returncode == 0:
                return None
            stderr = (r.stderr or r.stdout or "").strip()
            if len(stderr) > 300:
                stderr = stderr[:300] + "..."
            return f"copilot: auth probe failed (exit {r.returncode}): {stderr}"
        except subprocess.TimeoutExpired:
            return "copilot: auth probe timed out (>60s)"
        except FileNotFoundError:
            return "copilot: `copilot` CLI not found on PATH"
        except Exception as e:
            return f"copilot: auth probe error: {e}"

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        lines: list[str] = []
        in_tok = 0
        out_tok = 0
        # toolCallId -> tool name, so execution_complete results can be labelled.
        tool_names: dict[str, str] = {}

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
                    data = event.get("data", {}) or {}

                    if etype == "assistant.message":
                        text = data.get("content", "")
                        if text:
                            lines.append(f"[AGENT] {text}")
                            lines.append("")
                        for req in data.get("toolRequests", []) or []:
                            if not isinstance(req, dict):
                                continue
                            tname = req.get("name", "")
                            tid = req.get("toolCallId", "")
                            if tid:
                                tool_names[tid] = tname
                            targs = req.get("arguments", {})
                            try:
                                targs_str = json.dumps(targs, ensure_ascii=False)
                            except (TypeError, ValueError):
                                targs_str = str(targs)
                            if len(targs_str) > 1500:
                                targs_str = targs_str[:1500] + " ...(truncated)"
                            lines.append(f"[TOOL] {tname} {targs_str}")
                            lines.append("")
                        # copilot exposes per-message output tokens only; there
                        # is no input-token field in the JSONL stream.
                        out_tok += data.get("outputTokens", 0) or 0

                    elif etype == "tool.execution_start":
                        tid = data.get("toolCallId", "")
                        if tid:
                            tool_names[tid] = data.get("toolName", tool_names.get(tid, ""))

                    elif etype == "tool.execution_complete":
                        tid = data.get("toolCallId", "")
                        tname = tool_names.get(tid, "")
                        success = data.get("success", True)
                        result = data.get("result", {}) or {}
                        content = result.get("content", "") or result.get("detailedContent", "")
                        content = str(content)
                        if len(content) > 3000:
                            content = content[:1500] + "\n... (truncated) ...\n" + content[-1500:]
                        status = "ok" if success else "fail"
                        label = f"[TOOL_RESULT/{status}] {tname}".rstrip()
                        lines.append(label)
                        if content:
                            lines.append(content.rstrip())
                        lines.append("")

                    elif etype == "result":
                        exit_code = event.get("exitCode", "")
                        usage = event.get("usage", {}) or {}
                        prem = usage.get("premiumRequests")
                        summary = f"[RESULT exit={exit_code}]"
                        if prem is not None:
                            summary += f" premiumRequests={prem}"
                        lines.append(summary)
                        lines.append("")

        except FileNotFoundError:
            pass

        return "\n".join(lines), in_tok, out_tok
