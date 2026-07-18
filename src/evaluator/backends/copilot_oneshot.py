"""Strict one-shot backend using the official GitHub Copilot SDK."""

from __future__ import annotations

import os
from dataclasses import replace

from .base import detect_firewall_hosts
from .copilot import DEFAULT_MODEL
from .oneshot import OneShotBackend


class CopilotOneShotBackend(OneShotBackend):
    name = "copilot_oneshot"
    provider = "copilot"
    install_script = "install-copilot-sdk.sh"
    session_state_dir = None
    env_keys = ["COPILOT_GITHUB_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"]
    capabilities = replace(
        OneShotBackend.capabilities,
        cooperative_deadline=True,
        timeout_drain_grace=10.0,
    )

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def check_auth(self) -> str | None:
        if any(os.environ.get(key) for key in self.env_keys):
            return None
        return "copilot_oneshot: COPILOT_GITHUB_TOKEN, GH_TOKEN, or GITHUB_TOKEN not set"

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model) + ["api.github.com"]

    def validate_request_audit(self, audit: dict[str, object], request_count: int) -> bool:
        """Cross-check Copilot's wire evidence against the common audit."""

        return (
            super().validate_request_audit(audit, request_count)
            and audit.get("audit_scope") == "wire"
            and audit.get("wire_audited") is True
            and self._is_exact_count(audit.get("inference_requests"), request_count)
            and self._is_exact_count(audit.get("inference_attempts"), request_count)
            and self._is_exact_count(audit.get("unknown_requests"), 0)
            and self._is_exact_bool(audit.get("system_removed"), request_count == 1)
            and self._is_exact_bool(audit.get("tools_removed"), request_count == 1)
        )
