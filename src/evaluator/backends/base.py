"""Abstract base class for agent CLI backends."""

from __future__ import annotations

from abc import ABC, abstractmethod

BEDROCK_HOSTS = [
    "bedrock-runtime.us-east-1.amazonaws.com",
    "bedrock-runtime.us-east-2.amazonaws.com",
    "bedrock-runtime.us-west-2.amazonaws.com",
    "bedrock-runtime.eu-west-1.amazonaws.com",
    "bedrock-runtime.eu-central-1.amazonaws.com",
    "bedrock-runtime.ap-southeast-1.amazonaws.com",
    "bedrock-runtime.ap-northeast-1.amazonaws.com",
]

VERTEX_HOSTS = [
    "us-central1-aiplatform.googleapis.com",
    "us-east1-aiplatform.googleapis.com",
    "europe-west1-aiplatform.googleapis.com",
]

# All known LLM API hosts. Safe to allow all together since the general internal is still blocked (Google, GitHub etc.)
ALL_API_HOSTS = [
    "api.openai.com",
    "api.anthropic.com",
    "generativelanguage.googleapis.com",
    "api.deepseek.com",
    "api.githubcopilot.com",
    "api.business.githubcopilot.com",
    "api.enterprise.githubcopilot.com",
] + BEDROCK_HOSTS + VERTEX_HOSTS


def detect_firewall_hosts(model: str) -> list[str]:
    """All known LLM API hosts. Blocks general internet, allows any provider."""
    return ALL_API_HOSTS


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
