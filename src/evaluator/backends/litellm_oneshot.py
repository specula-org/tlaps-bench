"""Strict one-shot backend using LiteLLM's provider adapters."""

from __future__ import annotations

from .base import detect_firewall_hosts
from .litellm_common import DEFAULT_MODEL, ENV_KEYS, REASONING_EFFORT_VALUES, check_auth, credential_mounts
from .oneshot import OneShotBackend


class LiteLLMOneShotBackend(OneShotBackend):
    name = "litellm_oneshot"
    provider = "litellm"
    install_script = "install-litellm-oneshot.sh"
    env_keys = ENV_KEYS
    reasoning_effort_values = REASONING_EFFORT_VALUES

    def __init__(self, model: str | None = None):
        self.model = model or DEFAULT_MODEL

    def get_credential_mounts(self) -> list[str]:
        return credential_mounts(self.model)

    def check_auth(self) -> str | None:
        return check_auth(self.model, self.name)

    def firewall_hosts(self) -> list[str]:
        return detect_firewall_hosts(self.model)

    def validate_request_audit(self, audit: dict[str, object], request_count: int) -> bool:
        """Cross-check LiteLLM's adapter evidence against the common audit."""

        return (
            super().validate_request_audit(audit, request_count)
            and audit.get("audit_scope") == "adapter"
            and audit.get("wire_audited") is False
            and self._is_exact_count(audit.get("litellm_completion_invocations"), request_count)
            and audit.get("litellm_retries_disabled") is True
            and audit.get("system_supplied") is False
            and audit.get("tools_supplied") is False
        )
