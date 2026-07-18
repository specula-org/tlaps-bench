"""Strict one-shot backend using LiteLLM's provider adapters."""

from __future__ import annotations

from .litellm import LiteLLMBackend
from .oneshot import OneShotBackend


class LiteLLMOneShotBackend(OneShotBackend, LiteLLMBackend):
    name = "litellm_oneshot"
    provider = "litellm"
    install_script = "install-litellm-oneshot.sh"
