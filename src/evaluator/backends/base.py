"""Abstract base class for agent CLI backends."""

from __future__ import annotations

from abc import ABC, abstractmethod


class AgentBackend(ABC):
    name: str = ""
    install_script: str | None = None  # run at container start (e.g. "install-codex.sh")
    env_keys: list[str] = []  # host env vars to forward into container

    @abstractmethod
    def build_command(self, workspace: str, result_dir: str) -> list[str]:
        """Build the agent CLI command. Prompt is fed via stdin.

        Args:
            workspace: agent's working directory (will be the CLI's cwd).
            result_dir: directory for backend-specific output files.
        """

    @abstractmethod
    def parse_output(self, jsonl_path: str) -> tuple[str, int, int]:
        """Parse the backend's stdout dump into (transcript, input_tokens, output_tokens)."""

    def check_auth(self) -> str | None:
        """Host-side fast auth check. Returns None if OK, error string otherwise."""
        return None

    def firewall_hosts(self) -> list[str]:
        """API hosts that must be reachable."""
        return []
