"""Abstract base class for agent CLI backends."""

from __future__ import annotations

import os
from abc import ABC, abstractmethod
from pathlib import Path
from urllib.parse import urlparse

BEDROCK_HOSTS = [
    "bedrock-runtime.us-east-1.amazonaws.com",
    "bedrock-runtime.us-east-2.amazonaws.com",
    "bedrock-runtime.us-west-2.amazonaws.com",
    "bedrock-runtime.eu-west-1.amazonaws.com",
    "bedrock-runtime.eu-central-1.amazonaws.com",
    "bedrock-runtime.ap-southeast-1.amazonaws.com",
    "bedrock-runtime.ap-northeast-1.amazonaws.com",
]

# AWS STS endpoints for role assumption (needed when AWS_PROFILE uses role_arn)
STS_HOSTS = [
    "sts.amazonaws.com",
    "sts.us-east-1.amazonaws.com",
    "sts.us-east-2.amazonaws.com",
    "sts.us-west-2.amazonaws.com",
    "sts.eu-west-1.amazonaws.com",
    "sts.eu-central-1.amazonaws.com",
    "sts.ap-southeast-1.amazonaws.com",
    "sts.ap-northeast-1.amazonaws.com",
]

VERTEX_HOSTS = [
    "us-central1-aiplatform.googleapis.com",
    "us-east1-aiplatform.googleapis.com",
    "europe-west1-aiplatform.googleapis.com",
]

KIRO_HOSTS = [
    # API (CodeWhisperer/Q service)
    "q.us-east-1.amazonaws.com",
    "q.eu-central-1.amazonaws.com",
    # OIDC token refresh (IAM Identity Center)
    "oidc.us-east-1.amazonaws.com",
    "oidc.us-east-2.amazonaws.com",
    "oidc.us-west-2.amazonaws.com",
    "oidc.eu-central-1.amazonaws.com",
    "oidc.eu-west-1.amazonaws.com",
    "oidc.ap-southeast-1.amazonaws.com",
]

# All known LLM API hosts. Safe to allow all together since the general internet is still blocked (Google, GitHub etc.)
ALL_API_HOSTS = (
    [
        "api.openai.com",
        "chatgpt.com",  # Codex subscription auth (backend-api endpoint)
        "auth.openai.com",  # OAuth token exchange for ChatGPT login
        "api.anthropic.com",
        "console.anthropic.com",  # Claude Code OAuth token exchange
        "platform.claude.com",  # Claude Code OAuth token refresh (current endpoint)
        "generativelanguage.googleapis.com",
        "api.deepseek.com",
        "api.githubcopilot.com",
        "api.business.githubcopilot.com",
        "api.enterprise.githubcopilot.com",
        # Additional providers (pi backend, litellm)
        "api.groq.com",
        "api.mistral.ai",
        "openrouter.ai",
        "api.x.ai",
        "router.huggingface.co",
        "open.bigmodel.cn",  # Zhipu AI / GLM models
        "api.z.ai",  # Zhipu AI / GLM models
        "login.microsoftonline.com",
    ]
    + BEDROCK_HOSTS
    + STS_HOSTS
    + VERTEX_HOSTS
    + KIRO_HOSTS
)


def _azure_openai_hosts() -> list[str]:
    """Extract Azure OpenAI endpoint host(s) from environment variables.

    Azure OpenAI uses customer-specific hostnames (e.g.
    my-resource.openai.azure.com) that cannot be statically enumerated.
    """
    hosts: list[str] = []
    for var in ("AZURE_OPENAI_HOST", "AZURE_API_BASE", "AZURE_OPENAI_ENDPOINT"):
        val = os.environ.get(var, "").strip()
        if not val:
            continue
        parsed = urlparse(val).hostname if "://" in val else val.split("/")[0]
        if parsed and parsed not in hosts:
            hosts.append(parsed)
    return hosts


def detect_firewall_hosts(model: str) -> list[str]:
    """All known LLM API hosts. Blocks general internet, allows any provider."""
    return ALL_API_HOSTS + _azure_openai_hosts()


def has_aws_env_credentials() -> bool:
    """Whether AWS access-key credentials are available through env vars."""
    return bool(os.environ.get("AWS_ACCESS_KEY_ID") and os.environ.get("AWS_SECRET_ACCESS_KEY"))


def has_aws_bedrock_bearer_token() -> bool:
    """Whether Bedrock bearer-token auth is available through env vars."""
    return bool(os.environ.get("AWS_BEARER_TOKEN_BEDROCK"))


def has_aws_region() -> bool:
    """Whether an AWS region is available through env vars."""
    return bool(os.environ.get("AWS_REGION") or os.environ.get("AWS_DEFAULT_REGION"))


def needs_aws_shared_credentials() -> bool:
    """Whether a container needs ~/.aws for AWS SDK credential resolution."""
    return not (has_aws_bedrock_bearer_token() or has_aws_env_credentials())


def has_aws_shared_credentials() -> bool:
    """Whether host-side AWS shared credentials/config may be available."""
    return (Path.home() / ".aws").is_dir()


class AgentBackend(ABC):
    name: str = ""
    install_script: str | None = None  # run at container start (e.g. "install-codex.sh")
    env_keys: list[str] = []  # host env vars to forward into container
    credential_mounts: list[str] = []  # host credential dirs to copy into agent containers

    def get_credential_mounts(self) -> list[str]:
        """Credential directories this backend needs mounted for the current run."""
        return list(self.credential_mounts)

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
