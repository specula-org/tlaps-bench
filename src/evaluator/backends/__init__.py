"""Evaluator backend registry and public approach contracts."""

from .agentic import AgenticBackend as AgenticBackend
from .base import AgentBackend as AgentBackend
from .base import Backend
from .claude_code import ClaudeCodeBackend
from .codex import CodexBackend
from .copilot import CopilotBackend
from .copilot_oneshot import CopilotOneShotBackend
from .litellm import LiteLLMBackend
from .litellm_oneshot import LiteLLMOneShotBackend
from .oneshot import OneShotBackend as OneShotBackend
from .pi import PiBackend

_REGISTRY = {
    CodexBackend.name: CodexBackend,
    ClaudeCodeBackend.name: ClaudeCodeBackend,
    CopilotBackend.name: CopilotBackend,
    CopilotOneShotBackend.name: CopilotOneShotBackend,
    LiteLLMBackend.name: LiteLLMBackend,
    LiteLLMOneShotBackend.name: LiteLLMOneShotBackend,
    PiBackend.name: PiBackend,
}


def get_backend(name: str, model: str | None = None) -> Backend:
    if name not in _REGISTRY:
        raise ValueError(f"unknown backend {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name](model=model)


def list_backends() -> list[str]:
    return sorted(_REGISTRY)
