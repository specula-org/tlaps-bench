"""Provider configuration shared by agentic and one-shot LiteLLM backends."""

from __future__ import annotations

import os

from .base import (
    has_aws_bedrock_bearer_token,
    has_aws_env_credentials,
    has_aws_shared_credentials,
    needs_aws_shared_credentials,
)

DEFAULT_MODEL = "claude-sonnet-4-6"

ENV_KEYS = [
    "OPENAI_API_KEY",
    "ANTHROPIC_API_KEY",
    "GOOGLE_API_KEY",
    "GEMINI_API_KEY",
    "AZURE_OPENAI_API_KEY",
    "AZURE_API_BASE",
    "AZURE_API_VERSION",
    "DEEPSEEK_API_KEY",
    "AWS_ACCESS_KEY_ID",
    "AWS_SECRET_ACCESS_KEY",
    "AWS_REGION",
    "AWS_DEFAULT_REGION",
    "AWS_REGION_NAME",
]


def uses_bedrock(model: str) -> bool:
    return "bedrock" in model.lower()


def credential_mounts(model: str) -> list[str]:
    if uses_bedrock(model) and needs_aws_shared_credentials():
        return ["aws"]
    return []


def check_auth(model: str, backend_name: str) -> str | None:
    """Validate provider-specific credentials without coupling approaches."""

    normalized = model.lower()
    if "bedrock" in normalized:
        if has_aws_bedrock_bearer_token():
            if not (os.environ.get("AWS_REGION_NAME") or os.environ.get("AWS_REGION")):
                return f"{backend_name}: AWS_REGION_NAME or AWS_REGION required for bedrock bearer-token auth"
            return None
        if has_aws_env_credentials():
            if not (os.environ.get("AWS_REGION_NAME") or os.environ.get("AWS_REGION")):
                return f"{backend_name}: AWS_REGION_NAME or AWS_REGION required for bedrock model"
            return None
        if has_aws_shared_credentials():
            return None
        return f"{backend_name}: AWS credentials not found for bedrock model"
    if "anthropic" in normalized or "claude" in normalized:
        if os.environ.get("ANTHROPIC_API_KEY"):
            return None
        return f"{backend_name}: ANTHROPIC_API_KEY not set for anthropic model"
    if "gemini" in normalized or "google" in normalized:
        if os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY"):
            return None
        return f"{backend_name}: GOOGLE_API_KEY or GEMINI_API_KEY not set for google model"
    if "deepseek" in normalized:
        if os.environ.get("DEEPSEEK_API_KEY"):
            return None
        return f"{backend_name}: DEEPSEEK_API_KEY not set for deepseek model"
    if os.environ.get("OPENAI_API_KEY") or os.environ.get("AZURE_OPENAI_API_KEY"):
        return None
    return f"{backend_name}: OPENAI_API_KEY not set"
