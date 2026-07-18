"""Base class for tool-using, workspace-editing evaluator backends."""

from __future__ import annotations

from .base import Backend


class AgenticBackend(Backend):
    """An evaluator backend that edits its workspace through an agent loop."""

    approach = "agentic"
