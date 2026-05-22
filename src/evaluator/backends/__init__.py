"""Agent backend registry."""

from typing import Optional

from .base import AgentBackend
from .codex import CodexBackend
from .claude_code import ClaudeCodeBackend

_REGISTRY = {
    CodexBackend.name: CodexBackend,
    ClaudeCodeBackend.name: ClaudeCodeBackend,
}


def get_backend(name: str, model: Optional[str] = None) -> AgentBackend:
    if name not in _REGISTRY:
        raise ValueError(f"unknown backend {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name](model=model)


def list_backends() -> list[str]:
    return sorted(_REGISTRY)
