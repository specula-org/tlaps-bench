"""Abstract base class for agent CLI backends."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Tuple


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
    def parse_output(self, jsonl_path: str) -> Tuple[str, int, int]:
        """Parse the backend's stdout dump into (transcript, input_tokens, output_tokens)."""

    def required_env(self) -> list[str]:
        """Env vars that must be set for this backend to work."""
        return []

    def firewall_hosts(self) -> list[str]:
        """API hosts that must be reachable. For docs / entrypoint reference."""
        return []
