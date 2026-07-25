"""Strict one-shot backend using the official GitHub Copilot SDK."""

from __future__ import annotations

import os
from dataclasses import replace

from .base import detect_firewall_hosts
from .copilot import DEFAULT_MODEL
from .oneshot import OneShotBackend
from .oneshot_runner import COPILOT_MAX_INFERENCE_ATTEMPTS


class CopilotOneShotBackend(OneShotBackend):
    name = "copilot_oneshot"
    provider = "copilot"
    install_script = "install-copilot-sdk.sh"
    session_state_dir = None
    env_keys = ["COPILOT_GITHUB_TOKEN", "GH_TOKEN", "GITHUB_TOKEN"]
    reasoning_effort_values = ("low", "medium", "high", "xhigh")
    supports_max_output_tokens = True
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

        request_details = audit.get("inference_request_details")
        details_ok = isinstance(request_details, list) and len(request_details) == request_count
        if details_ok:
            endpoint = audit.get("endpoint")
            request_url_sha256 = audit.get("request_url_sha256")
            request_sha256 = audit.get("request_sha256")
            details_ok = all(
                isinstance(detail, dict)
                and self._is_exact_count(detail.get("attempt"), attempt)
                and isinstance(detail.get("stream_completed"), bool)
                and detail.get("endpoint") == endpoint
                and detail.get("request_url_sha256") == request_url_sha256
                and detail.get("request_sha256") == request_sha256
                for attempt, detail in enumerate(request_details, start=1)
            )
            details_ok = details_ok and (
                request_count == 0
                or (
                    isinstance(request_url_sha256, str)
                    and bool(request_url_sha256)
                    and isinstance(request_sha256, str)
                    and bool(request_sha256)
                )
            )

        output_limit_ok = self.max_output_tokens is None or (
            self._is_exact_count(audit.get("requested_max_output_tokens"), self.max_output_tokens)
            and (
                (
                    request_count == 0
                    and "runtime_max_output_tokens" not in audit
                    and "wire_max_output_tokens" not in audit
                )
                or (
                    request_count > 0
                    and self._is_exact_count(audit.get("wire_max_output_tokens"), self.max_output_tokens)
                )
            )
        )
        logical_agent_turns = audit.get("logical_agent_turns")
        logical_turn_ok = (
            self._is_exact_count(logical_agent_turns, 1)
            if request_count > 0
            else self._is_exact_count(logical_agent_turns, 0) or self._is_exact_count(logical_agent_turns, 1)
        )
        completed_responses = audit.get("completed_responses")
        completed_response_ok = self._is_exact_count(completed_responses, 0) or self._is_exact_count(
            completed_responses, 1
        )
        deadline_blocked_requests = audit.get("deadline_blocked_requests")
        deadline_blocks_ok = (
            isinstance(deadline_blocked_requests, int)
            and not isinstance(deadline_blocked_requests, bool)
            and deadline_blocked_requests >= 0
            and (audit.get("deadline_closed") is True or deadline_blocked_requests == 0)
        )
        return (
            super().validate_request_audit(audit, request_count)
            and not isinstance(request_count, bool)
            and 0 <= request_count <= COPILOT_MAX_INFERENCE_ATTEMPTS
            and audit.get("retries_enabled") is True
            and audit.get("retry_scope") == "incomplete_response"
            and self._is_exact_count(audit.get("max_inference_attempts"), COPILOT_MAX_INFERENCE_ATTEMPTS)
            and logical_turn_ok
            and completed_response_ok
            and audit.get("audit_scope") == "wire"
            and audit.get("wire_audited") is True
            and self._is_exact_count(audit.get("inference_requests"), request_count)
            and self._is_exact_count(audit.get("inference_attempts"), request_count)
            and deadline_blocks_ok
            and self._is_exact_count(audit.get("unknown_requests"), 0)
            and self._is_exact_bool(audit.get("system_removed"), request_count > 0)
            and self._is_exact_bool(audit.get("tools_removed"), request_count > 0)
            and details_ok
            and output_limit_ok
        )
