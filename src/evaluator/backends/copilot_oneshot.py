"""Strict one-shot backend using the official GitHub Copilot SDK."""

from __future__ import annotations

import os

from .base import detect_firewall_hosts
from .copilot import DEFAULT_MODEL, CopilotBackend
from .oneshot import OneShotBackend


class CopilotOneShotBackend(OneShotBackend, CopilotBackend):
    name = "copilot_oneshot"
    provider = "copilot"
    install_script = "install-copilot-sdk.sh"
    session_state_dir = None
    env_keys = ["COPILOT_GITHUB_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"]

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def check_auth(self) -> str | None:
        if any(os.environ.get(key) for key in self.env_keys):
            return None
        return "copilot_oneshot: COPILOT_GITHUB_TOKEN, GH_TOKEN, or GITHUB_TOKEN not set"

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model) + ["api.github.com"]
