"""Abstract base class for agent CLI backends."""

from __future__ import annotations

from abc import ABC, abstractmethod


class AgentBackend(ABC):
    name: str = ""

    @abstractmethod
    def build_command(self, workspace: str, jsonl_out_path: str) -> list[str]:
        """Build the agent CLI command. Prompt is fed via stdin.

        Args:
            workspace: agent's working directory (will be the CLI's cwd).
            jsonl_out_path: where the runner will redirect stdout.
                            Returned by reference for backends that need to embed
                            the path in flags (most don't — codex uses -o for last
                            message, claude streams to stdout).
        """

    @abstractmethod
    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        """Parse the backend's stdout dump into (transcript, input_tokens, output_tokens)."""

    def check_auth(self) -> str | None:
        """Verify the agent CLI can authenticate.

        Returns None if auth looks OK, or a human-readable error string that
        the runner will print and exit on.

        Each backend chooses how to verify — env var fast path, CLI status
        subcommand, or a minimal CLI probe — since users may authenticate
        via API key, OAuth (`claude /login` / `codex login`), or a subscription.
        Pre-flight should be quiet and ephemeral: do not leave session history.
        """
        return None

    def firewall_hosts(self) -> list[str]:
        """API hosts that must be reachable. For docs / entrypoint reference."""
        return []
