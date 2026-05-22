"""Agent backend registry."""

from .base import AgentBackend
from .codex import CodexBackend

_REGISTRY = {
    CodexBackend.name: CodexBackend,
}


def get_backend(name: str) -> AgentBackend:
    if name not in _REGISTRY:
        raise ValueError(f"unknown backend {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name]()


def list_backends() -> list[str]:
    return sorted(_REGISTRY)
