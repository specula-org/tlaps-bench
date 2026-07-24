"""Cursor CLI (`cursor-agent`) backend."""

from __future__ import annotations

import json
import os
import re
import subprocess
from ipaddress import ip_address
from urllib.parse import urlparse

from .agentic import AgenticBackend

DEFAULT_MODEL = "sonnet-4.5"
DEFAULT_API_ENDPOINT = "https://api2.cursor.sh"
_DNS_LABEL = re.compile(r"^[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?$")


class CursorBackend(AgenticBackend):
    name = "cursor"
    install_script = "install-cursor.sh"
    session_state_dir = None
    # CURSOR_API_KEY / endpoint let users route via an API key instead of the
    # mounted `cursor-agent login` credentials.
    env_keys = [
        "CURSOR_API_KEY",
        "CURSOR_API_ENDPOINT",
    ]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        # --force: run non-interactively with full tool access (implies workspace
        #   trust), since the Docker container is the isolation boundary.
        # --sandbox disabled: don't nest Cursor's own sandbox inside the container
        #   (avoids the unprivileged-userns/bwrap failure seen with other CLIs).
        return [
            "cursor-agent",
            "--print",
            "--output-format",
            "stream-json",
            "--force",
            "--sandbox",
            "disabled",
            "--workspace",
            workspace,
            "--model",
            self.model,
        ]

    def get_credential_mounts(self) -> list[str]:
        # API-key auth needs no mounted login credentials.
        if os.environ.get("CURSOR_API_KEY"):
            return []
        return ["cursor"]

    def check_auth(self) -> str | None:
        # Fast path: an API key is set.
        if os.environ.get("CURSOR_API_KEY"):
            return None
        # Slow path: ask the CLI whether it's logged in (local read of
        # ~/.config/cursor state; no session pollution).
        try:
            r = subprocess.run(
                ["cursor-agent", "status"],
                capture_output=True,
                text=True,
                timeout=15,
            )
            if r.returncode == 0 and "Logged in" in (r.stdout + r.stderr):
                return None
        except FileNotFoundError:
            return "cursor: `cursor-agent` CLI not found on PATH"
        except Exception:
            pass
        return "cursor: no auth detected. Set CURSOR_API_KEY or run `cursor-agent login`."

    def firewall_hosts(self) -> list[str]:
        """Allow only the configured Cursor API endpoint.

        The container firewall supports HTTPS on port 443 only, so reject
        endpoint values that it cannot enforce instead of silently widening
        egress or letting the run fail later inside Cursor.
        """
        endpoint = os.environ.get("CURSOR_API_ENDPOINT", DEFAULT_API_ENDPOINT).strip()
        try:
            parsed = urlparse(endpoint)
            port = parsed.port
        except ValueError as exc:
            raise ValueError(f"invalid CURSOR_API_ENDPOINT: {endpoint!r}") from exc

        if (
            parsed.scheme.lower() != "https"
            or not parsed.netloc
            or not parsed.hostname
            or parsed.username is not None
            or parsed.password is not None
            or port not in (None, 443)
        ):
            raise ValueError(
                f"CURSOR_API_ENDPOINT must be an absolute HTTPS URL on port 443 with a valid hostname, got {endpoint!r}"
            )

        try:
            hostname = parsed.hostname.encode("idna").decode("ascii").lower().rstrip(".")
            ip_address(hostname)
        except ValueError:
            labels = hostname.split(".")
            if not hostname or len(hostname) > 253 or not all(_DNS_LABEL.fullmatch(label) for label in labels):
                raise ValueError(
                    "CURSOR_API_ENDPOINT must be an absolute HTTPS URL on port 443 "
                    f"with a valid hostname, got {endpoint!r}"
                ) from None
        except UnicodeError as exc:
            raise ValueError(f"invalid CURSOR_API_ENDPOINT hostname: {parsed.hostname!r}") from exc
        else:
            raise ValueError(f"CURSOR_API_ENDPOINT must use a DNS hostname, got {endpoint!r}")

        return [hostname]

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

                    if etype == "assistant":
                        message = event.get("message", {})
                        content = message.get("content", [])
                        if isinstance(content, list):
                            for block in content:
                                if not isinstance(block, dict):
                                    continue
                                if block.get("type") == "text":
                                    text = block.get("text", "")
                                    if text:
                                        lines.append(f"[AGENT] {text}")
                                        lines.append("")

                    elif etype == "tool_call":
                        subtype = event.get("subtype", "")
                        tc = event.get("tool_call", {})
                        if not isinstance(tc, dict) or not tc:
                            continue
                        kind = next(iter(tc))
                        body = tc.get(kind) if isinstance(tc.get(kind), dict) else {}
                        args = body.get("args", {}) if isinstance(body, dict) else {}
                        if subtype == "started":
                            lines.append(f"[TOOL] {kind} {self._summarize_args(kind, args)}")
                            lines.append("")
                        elif subtype == "completed":
                            result = body.get("result") if isinstance(body, dict) else None
                            if result is not None:
                                lines.append(f"[TOOL_RESULT] {self._summarize_result(result)}")
                                lines.append("")

                    elif etype == "result":
                        subtype = event.get("subtype", "")
                        result_text = event.get("result", "")
                        if result_text:
                            lines.append(f"[RESULT/{subtype}] {result_text}")
                            lines.append("")
                        usage = event.get("usage", {})
                        if isinstance(usage, dict):
                            in_tok = (
                                usage.get("inputTokens", 0)
                                + usage.get("cacheReadTokens", 0)
                                + usage.get("cacheWriteTokens", 0)
                            )
                            out_tok = usage.get("outputTokens", 0)

                    elif etype == "error":
                        lines.append(f"[ERROR] {event.get('message', '')}")
                        lines.append("")
        except FileNotFoundError:
            pass

        return "\n".join(lines), in_tok, out_tok

    @staticmethod
    def _summarize_args(kind: str, args: dict) -> str:
        if not isinstance(args, dict):
            return ""
        for key in ("command", "path", "filePath", "query", "pattern"):
            val = args.get(key)
            if isinstance(val, str) and val:
                return val
        try:
            s = json.dumps(args, ensure_ascii=False)
        except (TypeError, ValueError):
            s = str(args)
        return s[:300]

    @staticmethod
    def _summarize_result(result: object) -> str:
        try:
            s = result if isinstance(result, str) else json.dumps(result, ensure_ascii=False)
        except (TypeError, ValueError):
            s = str(result)
        if len(s) > 3000:
            s = s[:1500] + "\n... (truncated) ...\n" + s[-1500:]
        return s.rstrip()
