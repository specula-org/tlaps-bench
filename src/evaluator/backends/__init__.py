"""Agent backend registry."""

from .base import AgentBackend
from .codex import CodexBackend
from .claude_code import ClaudeCodeBackend

_REGISTRY = {
    CodexBackend.name: CodexBackend,
    ClaudeCodeBackend.name: ClaudeCodeBackend,
}


def get_backend(name: str) -> AgentBackend:
    if name not in _REGISTRY:
        raise ValueError(f"unknown backend {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name]()


def list_backends() -> list[str]:
    return sorted(_REGISTRY)
