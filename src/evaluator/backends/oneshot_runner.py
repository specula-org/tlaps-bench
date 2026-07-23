"""Provider-neutral strict one-shot model runner.

The process reads one prompt from stdin and writes JSONL events to stdout.  The
LiteLLM path makes one completion call with retries disabled.  The Copilot path
uses the official SDK's request-handler seam to remove SDK-added context at the
wire boundary.  One logical Copilot turn may transparently retry an incomplete
request, but it can produce at most one complete assistant response.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import importlib.metadata
import json
import math
import os
import re
import sys
import tempfile
import time
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, Protocol
from urllib.parse import urlsplit

import httpx

try:
    from copilot import CopilotRequestHandler as _CopilotRequestHandler
except ImportError:  # The LiteLLM-only installation intentionally omits this dependency.

    class _CopilotRequestHandler:  # type: ignore[no-redef]
        async def send_request(self, _request: httpx.Request, _ctx: object) -> httpx.Response:
            raise RuntimeError("github-copilot-sdk is not installed")


_INFERENCE_ENDPOINTS = (
    "/chat/completions",
    "/responses",
    "/v1/messages",
    "/messages",
)
_AUXILIARY_ENDPOINTS = (
    "/models/session",
    "/models",
    "/policy",
)
_CONTEXT_AND_TOOL_KEYS = frozenset(
    {
        "context",
        "conversation",
        "developer",
        "developer_message",
        "function_call",
        "functions",
        "history",
        "input",
        "instructions",
        "messages",
        "parallel_tool_calls",
        "previous_response_id",
        "prompt",
        "system",
        "tool_choice",
        "tools",
    }
)
_SAFE_INFERENCE_CONTROL_KEYS = {
    "/responses": frozenset(
        {
            "include",
            "max_output_tokens",
            "model",
            "reasoning",
            "service_tier",
            "store",
            "stream",
            "temperature",
            "top_p",
            "truncation",
        }
    ),
    "/chat/completions": frozenset(
        {
            "frequency_penalty",
            "logit_bias",
            "logprobs",
            "max_completion_tokens",
            "max_tokens",
            "model",
            "n",
            "presence_penalty",
            "reasoning_effort",
            "seed",
            "service_tier",
            "stop",
            "stream",
            "stream_options",
            "temperature",
            "top_logprobs",
            "top_p",
            "verbosity",
        }
    ),
    "/v1/messages": frozenset(
        {
            "max_tokens",
            "model",
            "service_tier",
            "stop_sequences",
            "stream",
            "temperature",
            "thinking",
            "top_k",
            "top_p",
        }
    ),
    "/messages": frozenset(
        {
            "max_tokens",
            "model",
            "service_tier",
            "stop_sequences",
            "stream",
            "temperature",
            "thinking",
            "top_k",
            "top_p",
        }
    ),
}
_OUTPUT_TOKEN_FIELDS = {
    "/responses": frozenset({"max_output_tokens"}),
    "/chat/completions": frozenset({"max_completion_tokens", "max_tokens"}),
    "/v1/messages": frozenset({"max_tokens"}),
    "/messages": frozenset({"max_tokens"}),
}
_PREFERRED_OUTPUT_TOKEN_FIELD = {
    "/responses": "max_output_tokens",
    "/chat/completions": "max_completion_tokens",
    "/v1/messages": "max_tokens",
    "/messages": "max_tokens",
}
_FORBIDDEN_FORWARD_HEADERS = {
    "connection",
    "content-encoding",
    "content-length",
    "host",
    "keep-alive",
    "proxy-connection",
    "te",
    "trailer",
    "transfer-encoding",
    "upgrade",
}
_COPILOT_TOKEN_KEYS = ("COPILOT_GITHUB_TOKEN", "GH_TOKEN", "GITHUB_TOKEN")
# The pinned Copilot CLI currently performs one initial inference plus at most
# five native retries.  This benchmark-owned cap keeps a future runtime change
# from silently turning one logical turn into an unbounded number of requests.
COPILOT_MAX_INFERENCE_ATTEMPTS = 6
_COPILOT_CONTEXT_IDENTITY_FIELDS = ("agent_id", "parent_agent_id", "interaction_type")
_MAX_AUDIT_ERROR_LENGTH = 500


def _emit(event_type: str, **payload: object) -> None:
    print(json.dumps({"type": event_type, **payload}, ensure_ascii=False), flush=True)


def _nonnegative_int(value: object) -> int:
    if isinstance(value, bool):
        return 0
    try:
        return max(int(value), 0)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return 0


def _optional_nonnegative_int(value: object) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = int(value)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return None
    return parsed if parsed >= 0 else None


def _optional_nonnegative_float(value: object) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return None
    return parsed if parsed >= 0 and math.isfinite(parsed) else None


def _duration_secs(value: object) -> float | None:
    total_seconds = getattr(value, "total_seconds", None)
    if not callable(total_seconds):
        return None
    try:
        return _optional_nonnegative_float(total_seconds())
    except (TypeError, ValueError, OverflowError):
        return None


def _enum_value(value: object) -> str | None:
    candidate = getattr(value, "value", value)
    return candidate if isinstance(candidate, str) and candidate else None


def _get(value: object, name: str, default: object = None) -> object:
    if isinstance(value, dict):
        return value.get(name, default)
    return getattr(value, name, default)


def _copilot_event_model_output_kind(event: object) -> str | None:
    """Identify streaming SDK events that prove the model produced output."""

    event_type = _enum_value(_get(event, "type"))
    data = _get(event, "data")
    if event_type in {"assistant.message_delta", "assistant.reasoning_delta"}:
        delta = _get(data, "delta_content")
        return event_type if isinstance(delta, str) and delta else None
    if event_type == "assistant.reasoning":
        content = _get(data, "content")
        return event_type if isinstance(content, str) and content else None
    return event_type if event_type == "assistant.tool_call_delta" else None


def _inference_endpoint(url: str) -> str | None:
    path = urlsplit(url).path.lower().rstrip("/")
    for endpoint in _INFERENCE_ENDPOINTS:
        if path.endswith(endpoint):
            return endpoint
    return None


def _request_url_sha256(url: httpx.URL) -> str:
    """Hash the complete normalized wire target without exposing its query."""

    return hashlib.sha256(str(url).encode("utf-8")).hexdigest()


def _auxiliary_endpoint(url: str) -> str | None:
    path = urlsplit(url).path.lower().rstrip("/")
    for endpoint in _AUXILIARY_ENDPOINTS:
        if path.endswith(endpoint):
            return endpoint
    return None


def _assert_no_hidden_context(value: object) -> None:
    """Fail closed if a retained control field embeds another prompt schema."""
    if isinstance(value, dict):
        for key, nested in value.items():
            normalized = str(key).lower()
            if normalized in _CONTEXT_AND_TOOL_KEYS:
                raise RuntimeError(f"strict one-shot: retained hidden context field {key}")
            if normalized == "role" and str(nested).lower() in {
                "assistant",
                "developer",
                "system",
                "tool",
            }:
                raise RuntimeError(f"strict one-shot: retained hidden {nested} role")
            _assert_no_hidden_context(nested)
    elif isinstance(value, (list, tuple)):
        for item in value:
            _assert_no_hidden_context(item)


def _rewrite_inference_payload(endpoint: str, payload: object, prompt: str) -> dict[str, Any]:
    if not isinstance(payload, dict):
        raise RuntimeError("strict one-shot: inference body must be a JSON object")
    if endpoint not in _SAFE_INFERENCE_CONTROL_KEYS:
        raise RuntimeError(f"strict one-shot: unsupported inference endpoint {endpoint}")

    rewritten = {
        key: value for key, value in payload.items() if str(key).lower() in _SAFE_INFERENCE_CONTROL_KEYS[endpoint]
    }
    if endpoint == "/responses":
        canonical = [
            {
                "role": "user",
                "content": [{"type": "input_text", "text": prompt}],
                "type": "message",
            }
        ]
        rewritten["input"] = canonical
    elif endpoint in {"/chat/completions", "/v1/messages", "/messages"}:
        canonical = [{"role": "user", "content": prompt}]
        rewritten["messages"] = canonical
    else:  # The endpoint membership check above makes this unreachable.
        raise AssertionError(endpoint)

    for key, value in rewritten.items():
        if key not in {"input", "messages"}:
            _assert_no_hidden_context(value)
    canonical_key = "input" if endpoint == "/responses" else "messages"
    if rewritten.get(canonical_key) != canonical:
        raise RuntimeError("strict one-shot: failed to install the canonical user prompt")
    return rewritten


def _apply_output_token_limit(
    endpoint: str,
    payload: dict[str, Any],
    requested: int | None,
) -> tuple[int | None, int | None]:
    """Apply an explicit wire limit and return the runtime and forwarded values."""

    fields = _OUTPUT_TOKEN_FIELDS[endpoint]
    matches = [key for key in payload if str(key).lower() in fields]
    if len(matches) > 1:
        if requested is not None:
            raise RuntimeError("strict one-shot: ambiguous runtime output token limit")
        return None, None

    runtime_limit: int | None = None
    if matches:
        value = payload[matches[0]]
        if isinstance(value, int) and not isinstance(value, bool) and value > 0:
            runtime_limit = value
        elif requested is not None:
            raise RuntimeError("strict one-shot: invalid runtime output token limit")

    if requested is None:
        return runtime_limit, runtime_limit

    target = str(matches[0]).lower() if matches else _PREFERRED_OUTPUT_TOKEN_FIELD[endpoint]
    for key in matches:
        payload.pop(key)
    payload[target] = requested
    if payload.get(target) != requested:
        raise RuntimeError("strict one-shot: failed to install requested output token limit")
    return runtime_limit, requested


class StrictCopilotRequestHandler(_CopilotRequestHandler):
    """Audit one Copilot turn and bound retries before its complete response."""

    def __init__(
        self,
        prompt: str,
        model: str | None = None,
        reasoning_effort: str | None = None,
        max_output_tokens: int | None = None,
    ) -> None:
        if max_output_tokens is not None and (
            not isinstance(max_output_tokens, int) or isinstance(max_output_tokens, bool) or max_output_tokens <= 0
        ):
            raise ValueError("max_output_tokens must be a positive integer")
        self._prompt = prompt
        self.model = model
        self.reasoning_effort = reasoning_effort
        self.requested_max_output_tokens = max_output_tokens
        self._expected_session_id: str | None = None
        self._expected_request_context: tuple[object, ...] | None = None
        self._deadline: float | None = None
        self._frozen = False
        self._logical_agent_turns = 0
        self._response_complete = False
        self._forward_tasks: set[asyncio.Task[Any]] = set()
        self._inference_forward_tasks: set[asyncio.Task[Any]] = set()
        self._inference_request_details: list[dict[str, object]] = []
        self.inference_attempts = 0
        self.forwarded_inference_requests = 0
        self.blocked_requests = 0
        self.deadline_blocked_requests = 0
        self.unknown_requests = 0
        self.endpoint: str | None = None
        self.request_url_sha256: str | None = None
        self.request_sha256: str | None = None
        self.runtime_max_output_tokens: int | None = None
        self.wire_max_output_tokens: int | None = None
        self._inference_status_code: int | None = None
        self._inference_failure_retryable: bool | None = None
        self._aux_status_code: int | None = None
        self._aux_failure_retryable: bool | None = None
        self._last_forward_kind: str | None = None
        self.system_removed = False
        self.tools_removed = False

    def bind_session(self, session_id: str) -> None:
        if not session_id:
            raise RuntimeError("strict one-shot: Copilot session has no id")
        if self._expected_session_id is not None and self._expected_session_id != session_id:
            raise RuntimeError("strict one-shot: handler cannot be rebound to another session")
        self._expected_session_id = session_id

    def set_deadline(self, deadline: float | None) -> None:
        """Bind the benchmark deadline before the SDK can start inference."""

        if self._deadline is not None and deadline != self._deadline:
            raise RuntimeError("strict one-shot: handler deadline cannot be rebound")
        self._deadline = deadline
        if deadline is not None and time.time() >= deadline:
            self.freeze()

    def begin_agent_turn(self) -> None:
        """Open the sole logical ``send_and_wait`` scope."""

        if self._logical_agent_turns != 0:
            raise RuntimeError("strict one-shot: more than one logical agent turn")
        if self._response_complete:
            raise RuntimeError("strict one-shot: agent turn started after a complete response")
        self._logical_agent_turns = 1

    def seal_after_response(self) -> None:
        """Close inference without cancelling the stream that delivered usage."""

        if self._logical_agent_turns != 1 or self.forwarded_inference_requests == 0:
            raise RuntimeError("strict one-shot: response arrived outside the logical agent turn")
        self._response_complete = True

    def freeze(self) -> None:
        """Atomically close inference and cancel any forwarding work in flight."""

        self._frozen = True
        try:
            current = asyncio.current_task()
        except RuntimeError:
            current = None
        for task in tuple(self._forward_tasks):
            if task is not current:
                task.cancel()

    def _inference_closed(self) -> bool:
        if self._frozen:
            return True
        if self._deadline is not None and time.time() >= self._deadline:
            self.freeze()
            return True
        return False

    @staticmethod
    def _request_context(ctx: object) -> tuple[object, ...]:
        return tuple(getattr(ctx, field, None) for field in _COPILOT_CONTEXT_IDENTITY_FIELDS)

    @staticmethod
    def _audit_error(exc: BaseException) -> str:
        message = str(exc)
        return message[:_MAX_AUDIT_ERROR_LENGTH] if message else type(exc).__name__

    def _latest_inference_detail(self) -> dict[str, object] | None:
        return self._inference_request_details[-1] if self._inference_request_details else None

    def _record_inference_failure(
        self,
        *,
        status_code: int | None = None,
        retryable: bool | None = None,
        exc: BaseException | None = None,
        detail: dict[str, object] | None = None,
    ) -> None:
        detail = detail or self._latest_inference_detail()
        if detail is None:
            return
        if self._detail_retryability(detail) is False:
            return
        if status_code is not None:
            detail["status_code"] = status_code
        if retryable is not None:
            detail["retryable"] = retryable
        if exc is not None:
            detail["error_type"] = type(exc).__name__
            detail["error"] = self._audit_error(exc)

    def record_event_failure(self, event: object, retryable: bool | None) -> None:
        """Attach a structured runtime failure to the active wire attempt."""

        detail = self._latest_inference_detail()
        if detail is None:
            return
        data = _get(event, "data")
        event_type = _enum_value(_get(event, "type"))
        message = _get(data, "message")
        if not isinstance(message, str):
            message = _get(data, "error_message")
        if self._detail_retryability(detail) is False:
            if retryable is False:
                if event_type and "failure_event" not in detail:
                    detail["failure_event"] = event_type
                if isinstance(message, str) and message and "error" not in detail:
                    detail["error"] = message[:_MAX_AUDIT_ERROR_LENGTH]
            return
        status_code = _status_code(_get(data, "status_code"))
        if status_code is None:
            status_code = _status_code(_get(data, "statusCode"))
        if status_code is not None:
            detail["status_code"] = status_code
        if retryable is not None:
            detail["retryable"] = retryable
        if event_type:
            detail["failure_event"] = event_type
        if isinstance(message, str) and message:
            detail["error"] = message[:_MAX_AUDIT_ERROR_LENGTH]

    @staticmethod
    def _detail_retryability(detail: dict[str, object]) -> bool | None:
        status_code = _status_code(detail.get("status_code"))
        retryable = detail.get("retryable")
        return _recorded_provider_retryability(
            status_code,
            retryable if isinstance(retryable, bool) else None,
        )

    def _retry_block_reason(
        self,
        *,
        endpoint: str,
        request_url_sha256: str,
        request_sha256: str,
        ctx: object,
    ) -> str | None:
        if self._response_complete:
            return "strict one-shot: blocked inference request after the complete response"
        if self.forwarded_inference_requests >= COPILOT_MAX_INFERENCE_ATTEMPTS:
            return "strict one-shot: blocked inference request after the retry limit"
        if endpoint != self.endpoint:
            return "strict one-shot: blocked inference retry with a changed endpoint"
        if request_url_sha256 != self.request_url_sha256:
            return "strict one-shot: blocked inference retry with a changed target URL"
        if request_sha256 != self.request_sha256:
            return "strict one-shot: blocked inference retry with a changed request"
        if self._request_context(ctx) != self._expected_request_context:
            return "strict one-shot: blocked inference retry with a changed agent context"
        detail = self._latest_inference_detail()
        if detail is not None and self._detail_retryability(detail) is False:
            return "strict one-shot: blocked inference retry after a permanent provider error"
        return None

    def permanent_failure_message(self) -> str | None:
        """Return the first persisted permanent provider failure, if any."""

        for detail in self._inference_request_details:
            if self._detail_retryability(detail) is not False:
                continue
            message = detail.get("error")
            if isinstance(message, str) and message:
                return message
            status_code = detail.get("status_code")
            if isinstance(status_code, int) and not isinstance(status_code, bool):
                return f"HTTP {status_code}"
        return None

    async def _forward_http(self, request: httpx.Request, exchange: object, ctx: object) -> None:
        """Track the SDK's complete response-stream forwarding lifecycle."""

        task = asyncio.current_task()
        inference_request = _inference_endpoint(str(request.url)) is not None
        detail_count_before = len(self._inference_request_details)
        if task is not None:
            self._forward_tasks.add(task)
            if inference_request:
                self._inference_forward_tasks.add(task)
        try:
            await super()._forward_http(request, exchange, ctx)  # type: ignore[attr-defined]
        except Exception as exc:
            retryability = _provider_error_retryability(exc)
            inference = inference_request
            auxiliary = _auxiliary_endpoint(str(request.url)) is not None
            status = _exception_status_code(exc)
            attempt_detail = (
                self._inference_request_details[detail_count_before]
                if inference and len(self._inference_request_details) == detail_count_before + 1
                else None
            )
            if attempt_detail is not None:
                self._record_inference_failure(
                    status_code=status,
                    retryable=retryability,
                    exc=exc,
                    detail=attempt_detail,
                )
            if retryability is not None and (inference or auxiliary):
                status_attr = "_inference_status_code" if inference else "_aux_status_code"
                retryable_attr = "_inference_failure_retryable" if inference else "_aux_failure_retryable"
                if status is not None:
                    setattr(self, status_attr, status)
                setattr(self, retryable_attr, retryability)
                self._last_forward_kind = "inference" if inference else "aux"
            raise
        else:
            if _inference_endpoint(str(request.url)) is not None:
                detail = self._latest_inference_detail()
                if detail is not None:
                    detail["stream_completed"] = True
        finally:
            if task is not None:
                self._forward_tasks.discard(task)
                self._inference_forward_tasks.discard(task)

    async def _forward(self, request: httpx.Request, ctx: object) -> httpx.Response:
        return await super().send_request(request, ctx)

    async def _forward_with_evidence(
        self,
        request: httpx.Request,
        ctx: object,
        *,
        inference: bool,
    ) -> httpx.Response:
        status_attr = "_inference_status_code" if inference else "_aux_status_code"
        retryable_attr = "_inference_failure_retryable" if inference else "_aux_failure_retryable"
        kind = "inference" if inference else "aux"
        setattr(self, status_attr, None)
        setattr(self, retryable_attr, None)
        try:
            response = await self._forward(request, ctx)
        except Exception as exc:
            status_code = _exception_status_code(exc)
            retryability = _provider_error_retryability(exc)
            setattr(self, status_attr, status_code)
            setattr(self, retryable_attr, retryability)
            self._last_forward_kind = kind
            if inference:
                self._record_inference_failure(
                    status_code=status_code,
                    retryable=retryability,
                    exc=exc,
                )
            raise
        setattr(self, status_attr, response.status_code)
        retryability = _http_response_retryability(response.status_code)
        setattr(
            self,
            retryable_attr,
            retryability,
        )
        self._last_forward_kind = kind
        if inference:
            self._record_inference_failure(
                status_code=response.status_code,
                retryable=retryability,
            )
        return response

    async def send_request(self, request: httpx.Request, ctx: object) -> httpx.Response:
        endpoint = _inference_endpoint(str(request.url))
        if endpoint is None:
            if _auxiliary_endpoint(str(request.url)) is not None:
                return await self._forward_with_evidence(request, ctx, inference=False)
            self.blocked_requests += 1
            self.unknown_requests += 1
            raise RuntimeError("strict one-shot: blocked unknown model-layer endpoint")

        if self._inference_closed():
            self.deadline_blocked_requests += 1
            raise RuntimeError("strict one-shot: blocked inference request after benchmark deadline")

        self.inference_attempts += 1
        if self.endpoint is None:
            self.endpoint = endpoint
        if self._logical_agent_turns != 1:
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: inference request outside the logical agent turn")
        current_task = asyncio.current_task()
        if any(task is not current_task for task in self._inference_forward_tasks):
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: blocked concurrent inference request")
        session_id = getattr(ctx, "session_id", None)
        if self._expected_session_id is None or session_id != self._expected_session_id:
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: inference request has an unexpected session id")
        if request.method.upper() != "POST":
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: inference request must use POST")

        try:
            payload = json.loads(request.content)
            rewritten_payload = _rewrite_inference_payload(endpoint, payload, self._prompt)
            runtime_limit, wire_limit = _apply_output_token_limit(
                endpoint,
                rewritten_payload,
                self.requested_max_output_tokens,
            )
            body = json.dumps(
                rewritten_payload,
                ensure_ascii=False,
                allow_nan=False,
                separators=(",", ":"),
            ).encode("utf-8")
        except RuntimeError:
            self.blocked_requests += 1
            raise
        except (UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: invalid inference request body") from exc
        request_sha256 = hashlib.sha256(body).hexdigest()
        request_url_sha256 = _request_url_sha256(request.url)

        if self.forwarded_inference_requests == 0:
            self._expected_request_context = self._request_context(ctx)
            self.request_url_sha256 = request_url_sha256
            self.request_sha256 = request_sha256
            self.runtime_max_output_tokens = runtime_limit
            self.wire_max_output_tokens = wire_limit
        else:
            retry_block_reason = self._retry_block_reason(
                endpoint=endpoint,
                request_url_sha256=request_url_sha256,
                request_sha256=request_sha256,
                ctx=ctx,
            )
            if retry_block_reason is not None:
                self.blocked_requests += 1
                raise RuntimeError(retry_block_reason)

        headers = [
            (name, value)
            for name, value in request.headers.multi_items()
            if name.lower() not in _FORBIDDEN_FORWARD_HEADERS
        ]
        rewritten = httpx.Request(request.method, request.url, headers=headers, content=body)

        # Reserve this bounded forwarding slot before the await. A concurrent
        # attempt therefore cannot observe a stale request count.
        if self._inference_closed():
            self.inference_attempts -= 1
            self.deadline_blocked_requests += 1
            raise RuntimeError("strict one-shot: blocked inference request after benchmark deadline")
        self.forwarded_inference_requests += 1
        detail: dict[str, object] = {
            "attempt": self.forwarded_inference_requests,
            "endpoint": endpoint,
            "request_url_sha256": request_url_sha256,
            "request_sha256": request_sha256,
            "stream_completed": False,
        }
        request_id = getattr(ctx, "request_id", None)
        if isinstance(request_id, str) and request_id:
            detail["request_id"] = request_id
        self._inference_request_details.append(detail)
        self.system_removed = True
        self.tools_removed = True
        forward_task = asyncio.create_task(self._forward_with_evidence(rewritten, ctx, inference=True))
        self._forward_tasks.add(forward_task)
        self._inference_forward_tasks.add(forward_task)
        try:
            return await forward_task
        finally:
            self._forward_tasks.discard(forward_task)
            self._inference_forward_tasks.discard(forward_task)

    async def open_websocket(self, _ctx: object) -> object:
        self.inference_attempts += 1
        self.blocked_requests += 1
        raise RuntimeError("strict one-shot: WebSocket inference is disabled")

    def assert_complete(self) -> None:
        if (
            self._logical_agent_turns != 1
            or not self._response_complete
            or not 1 <= self.forwarded_inference_requests <= COPILOT_MAX_INFERENCE_ATTEMPTS
            or self.inference_attempts != self.forwarded_inference_requests
            or self.blocked_requests != 0
        ):
            raise RuntimeError("strict one-shot: logical agent turn did not produce one clean response")

    def audit(self) -> dict[str, object]:
        contract_ok = (
            self.blocked_requests == 0
            and self.inference_attempts == self.forwarded_inference_requests
            and self.forwarded_inference_requests <= COPILOT_MAX_INFERENCE_ATTEMPTS
            and self._logical_agent_turns <= 1
            and (not self._response_complete or self._logical_agent_turns == 1)
            and (
                self.forwarded_inference_requests == 0
                or (
                    self._logical_agent_turns == 1
                    and self.system_removed is True
                    and self.tools_removed is True
                    and self.request_url_sha256 is not None
                    and len(self._inference_request_details) == self.forwarded_inference_requests
                )
            )
            and (
                self.requested_max_output_tokens is None
                or self.forwarded_inference_requests == 0
                or self.wire_max_output_tokens == self.requested_max_output_tokens
            )
        )
        audit: dict[str, object] = {
            "provider": "copilot",
            "model_requests": self.forwarded_inference_requests,
            "request_attempts": self.inference_attempts,
            "system_prompt_present": self.forwarded_inference_requests > 0 and self.system_removed is not True,
            "tools_present": self.forwarded_inference_requests > 0 and self.tools_removed is not True,
            "retries_enabled": True,
            "retry_scope": "incomplete_response",
            "max_inference_attempts": COPILOT_MAX_INFERENCE_ATTEMPTS,
            "logical_agent_turns": self._logical_agent_turns,
            "completed_responses": int(self._response_complete),
            "audit_scope": "wire",
            "contract_ok": contract_ok,
            "wire_audited": True,
            "inference_requests": self.forwarded_inference_requests,
            "inference_attempts": self.inference_attempts,
            "blocked_requests": self.blocked_requests,
            "deadline_blocked_requests": self.deadline_blocked_requests,
            "unknown_requests": self.unknown_requests,
            "system_removed": self.system_removed,
            "tools_removed": self.tools_removed,
            "deadline_closed": self._frozen,
            "inference_request_details": [dict(detail) for detail in self._inference_request_details],
        }
        if self.model is not None:
            audit["model"] = self.model
        if self.reasoning_effort is not None:
            audit["reasoning_effort"] = self.reasoning_effort
        if self.requested_max_output_tokens is not None:
            audit["requested_max_output_tokens"] = self.requested_max_output_tokens
        if self.runtime_max_output_tokens is not None:
            audit["runtime_max_output_tokens"] = self.runtime_max_output_tokens
        if self.wire_max_output_tokens is not None:
            audit["wire_max_output_tokens"] = self.wire_max_output_tokens
        if self.endpoint is not None:
            audit["endpoint"] = self.endpoint
        if self.request_url_sha256 is not None:
            audit["request_url_sha256"] = self.request_url_sha256
        if self.request_sha256 is not None:
            audit["request_sha256"] = self.request_sha256
        return audit


@dataclass(frozen=True)
class ProviderResult:
    text: str
    input_tokens: int | None
    output_tokens: int | None
    audit: dict[str, object]
    # One entry per model request. Explicit core token fields distinguish a
    # measured zero from unavailable usage in provider-neutral completeness.
    usage_details: tuple[dict[str, object], ...] = ()


class ProviderRunError(RuntimeError):
    """Provider failure carrying the audit and usage accumulated before it failed."""

    def __init__(
        self,
        message: str,
        audit: dict[str, object],
        input_tokens: int | None = None,
        output_tokens: int | None = None,
        usage_details: tuple[dict[str, object], ...] = (),
        retryable: bool = False,
    ) -> None:
        super().__init__(message)
        self.audit = audit
        self.input_tokens = _optional_nonnegative_int(input_tokens)
        self.output_tokens = _optional_nonnegative_int(output_tokens)
        self.usage_details = usage_details
        self.retryable = retryable is True


class ProviderTimeoutError(ProviderRunError):
    """The provider-side wait reached the benchmark's propagated deadline."""


_TRANSIENT_HTTP_STATUS_CODES = frozenset({408, 425, 429, 500, 502, 503, 504, 529})
_TRANSIENT_ERROR_CLASS_NAMES = frozenset(
    {
        "APIConnectionError",
        "APITimeoutError",
        "InternalServerError",
        "RateLimitError",
        "ServiceUnavailableError",
        "Timeout",
    }
)
_PERMANENT_ERROR_CLASS_NAMES = frozenset(
    {
        "AuthenticationError",
        "BadRequestError",
        "ContextWindowExceededError",
        "NotFoundError",
        "PermissionDeniedError",
        "UnprocessableEntityError",
    }
)


def _exception_chain(exc: BaseException) -> tuple[BaseException, ...]:
    chain: list[BaseException] = []
    seen: set[int] = set()
    current: BaseException | None = exc
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        chain.append(current)
        current = current.__cause__ or current.__context__
    return tuple(chain)


def _status_code(value: object) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and 100 <= value <= 599:
        return value
    return None


def _structured_status_code(value: object, *, depth: int = 0) -> int | None:
    if depth > 3 or not isinstance(value, dict):
        return None
    for key in ("status_code", "statusCode", "http_status", "httpStatus", "status"):
        status = _status_code(value.get(key))
        if status is not None:
            return status
    for key in ("data", "error", "response", "cause", "details"):
        status = _structured_status_code(value.get(key), depth=depth + 1)
        if status is not None:
            return status
    return None


def _exception_status_code(exc: BaseException) -> int | None:
    for current in _exception_chain(exc):
        status = _status_code(getattr(current, "status_code", None))
        if status is not None:
            return status
        response = getattr(current, "response", None)
        status = _status_code(getattr(response, "status_code", None))
        if status is not None:
            return status
        status = _structured_status_code(getattr(current, "data", None))
        if status is not None:
            return status
    return None


def _is_retryable_http_status(status: int | None) -> bool:
    return status in _TRANSIENT_HTTP_STATUS_CODES


def _http_response_retryability(status: int) -> bool | None:
    """Classify a response status, leaving Copilot's two 400 shapes provisional."""

    if status == 400:
        return None
    if status >= 400:
        return _is_retryable_http_status(status)
    return None


def _provider_error_retryability(exc: BaseException, *, status_code: int | None = None) -> bool | None:
    """Classify an error as transient, permanent, or unknown."""

    current_status = _exception_status_code(exc)
    if current_status is not None and current_status >= 400:
        return _is_retryable_http_status(current_status)
    chain = _exception_chain(exc)
    class_names = {base.__name__ for current in chain for base in type(current).__mro__}
    if class_names.intersection(_PERMANENT_ERROR_CLASS_NAMES):
        return False

    for current in chain:
        current_class_names = {base.__name__ for base in type(current).__mro__}
        if "JsonRpcError" not in current_class_names or getattr(current, "code", None) != -32603:
            continue
        message = getattr(current, "message", None)
        if (
            isinstance(message, str)
            and message.startswith("Request session.create failed with message:")
            and (
                "network fetch failed:" in message
                or (
                    "Failed to validate SDK token" in message
                    and any(f"({status})" in message for status in _TRANSIENT_HTTP_STATUS_CODES)
                )
            )
        ):
            return True

    fallback_status = _status_code(status_code)
    if fallback_status is not None and fallback_status >= 400:
        return _is_retryable_http_status(fallback_status)
    if any(isinstance(current, (ConnectionError, TimeoutError, httpx.TransportError)) for current in chain):
        return True
    if class_names.intersection(_TRANSIENT_ERROR_CLASS_NAMES):
        return True
    if "ProcessExitedError" in class_names:
        return True
    if any(type(current) is RuntimeError and str(current).startswith("CLI process exited") for current in chain):
        return True
    return None


def _is_retryable_provider_error(exc: BaseException, *, status_code: int | None = None) -> bool:
    """Fail closed unless structured evidence identifies a transient failure."""

    return _provider_error_retryability(exc, status_code=status_code) is True


def _recorded_provider_retryability(status_code: int | None, retryable: bool | None) -> bool | None:
    status = _status_code(status_code)
    if status == 400:
        return retryable
    if status is not None and status >= 400:
        return _is_retryable_http_status(status)
    return retryable


def _copilot_event_error_retryability(events: list[object]) -> bool | None:
    """Classify structured SDK failure events, with permanent evidence winning."""

    saw_transient = False
    for event in events:
        event_type = _enum_value(_get(event, "type"))
        if event_type not in {"session.error", "model.call_failure"}:
            continue
        data = _get(event, "data")
        for field in ("retryable", "recoverable"):
            value = _get(data, field)
            if value is False:
                return False
            if value is True:
                saw_transient = True
        bad_request_kind = _enum_value(_get(data, "bad_request_kind"))
        if bad_request_kind is None:
            bad_request_kind = _enum_value(_get(data, "badRequestKind"))
        if bad_request_kind == "structured_error":
            return False
        if bad_request_kind == "bodyless":
            saw_transient = True
            continue
        error_type = _get(data, "error_type")
        if not isinstance(error_type, str):
            error_type = _get(data, "errorType")
        if isinstance(error_type, str) and error_type.lower() in {
            "authentication",
            "bad_request",
            "invalid_model",
            "invalid_request",
            "not_found",
            "permission_denied",
        }:
            return False
        status = _status_code(_get(data, "status_code"))
        if status is None:
            status = _status_code(_get(data, "statusCode"))
        if status is None or status < 400:
            message_field = "message" if event_type == "session.error" else "error_message"
            message = _get(data, message_field)
            if isinstance(message, str):
                status_match = re.search(r"(?:^|Last error:\s+)(\d{3})(?:\s|$)", message)
                message_status = _status_code(int(status_match.group(1))) if status_match else None
                if message_status is not None:
                    if not _is_retryable_http_status(message_status):
                        return False
                    saw_transient = True
                elif message.endswith("All connection attempts failed"):
                    saw_transient = True
        else:
            if not _is_retryable_http_status(status):
                return False
            saw_transient = True
    return True if saw_transient else None


def _copilot_bodyless_bad_request_observed(events: list[object]) -> bool:
    """Return whether the runtime identified a transient bodyless HTTP 400."""

    for event in events:
        if _enum_value(_get(event, "type")) != "model.call_failure":
            continue
        data = _get(event, "data")
        kind = _enum_value(_get(data, "bad_request_kind"))
        if kind is None:
            kind = _enum_value(_get(data, "badRequestKind"))
        if kind == "bodyless":
            return True
    return False


class _CopilotDeadlineExceeded(RuntimeError):
    """Internal marker for the deadline owned by this runner."""


def _response_text(response: object) -> str:
    choices = _get(response, "choices", [])
    if not isinstance(choices, (list, tuple)) or len(choices) != 1:
        raise RuntimeError("one-shot provider returned an invalid choice count")
    message = _get(choices[0], "message")
    content = _get(message, "content")
    if not isinstance(content, str) or not content.strip():
        raise RuntimeError("one-shot provider returned no text response")
    return content


def _response_finish_reason(response: object) -> str | None:
    choices = _get(response, "choices", [])
    if not isinstance(choices, (list, tuple)) or len(choices) != 1:
        return None
    finish_reason = _get(choices[0], "finish_reason")
    return finish_reason if isinstance(finish_reason, str) and finish_reason else None


def _litellm_max_tokens(litellm: object, model: str) -> int:
    """Use pinned LiteLLM metadata without a provider lookup or network preflight."""
    model_cost = getattr(litellm, "model_cost", {})
    if not isinstance(model_cost, dict):
        return 32_768
    candidates = (model, model.split("/", 1)[-1])
    for candidate in candidates:
        metadata = model_cost.get(candidate)
        if not isinstance(metadata, dict):
            continue
        for key in ("max_output_tokens", "max_tokens"):
            limit = metadata.get(key)
            if isinstance(limit, int) and not isinstance(limit, bool) and limit > 0:
                return min(32_768, limit)
    return 32_768


def _litellm_audit(
    prompt: str,
    model: str,
    max_tokens: int = 32_768,
    reasoning_effort: str | None = None,
) -> dict[str, object]:
    request: dict[str, object] = {"model": model, "messages": [{"role": "user", "content": prompt}]}
    if reasoning_effort is not None:
        request["reasoning_effort"] = reasoning_effort
    audit: dict[str, object] = {
        "provider": "litellm",
        "model": model,
        "model_requests": 0,
        "request_attempts": 0,
        "blocked_requests": 0,
        "system_prompt_present": False,
        "tools_present": False,
        "retries_enabled": False,
        "audit_scope": "adapter",
        "contract_ok": True,
        "litellm_completion_invocations": 0,
        "wire_audited": False,
        "litellm_retries_disabled": True,
        "request_sha256": hashlib.sha256(
            json.dumps(request, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        ).hexdigest(),
        "system_supplied": False,
        "tools_supplied": False,
        "max_tokens": max_tokens,
    }
    if reasoning_effort is not None:
        audit["reasoning_effort"] = reasoning_effort
    return audit


def run_litellm(prompt: str, model: str, reasoning_effort: str | None = None) -> ProviderResult:
    request: dict[str, object] = {"model": model, "messages": [{"role": "user", "content": prompt}]}
    if reasoning_effort is not None:
        request["reasoning_effort"] = reasoning_effort
    audit = _litellm_audit(prompt, model, reasoning_effort=reasoning_effort)
    try:
        import litellm
    except ImportError as exc:
        raise ProviderRunError("litellm is not installed", audit) from exc

    max_tokens = _litellm_max_tokens(litellm, model)
    audit["max_tokens"] = max_tokens

    # This disables LiteLLM's own retry orchestration. Provider transports may
    # have behavior below this adapter boundary, so this is intentionally not
    # described as a wire-level request count.
    input_tokens: int | None = None
    output_tokens: int | None = None
    usage_details: tuple[dict[str, object], ...] = ()
    try:
        audit["litellm_completion_invocations"] = 1
        audit["model_requests"] = 1
        audit["request_attempts"] = 1
        response = litellm.completion(
            **request,
            stream=False,
            max_tokens=max_tokens,
            num_retries=0,
        )
        usage = _get(response, "usage")
        request_input = _optional_nonnegative_int(_get(usage, "prompt_tokens"))
        if request_input is None:
            request_input = _optional_nonnegative_int(_get(usage, "input_tokens"))
        request_output = _optional_nonnegative_int(_get(usage, "completion_tokens"))
        if request_output is None:
            request_output = _optional_nonnegative_int(_get(usage, "output_tokens"))
        input_tokens = request_input
        output_tokens = request_output
        detail: dict[str, object] = {"source": "litellm_response_usage"}
        optional_values: dict[str, object | None] = {
            "input_tokens": request_input,
            "output_tokens": request_output,
            "model": _enum_value(_get(response, "model")),
        }
        detail.update({key: value for key, value in optional_values.items() if value is not None})
        usage_details = (detail,)
        text = _response_text(response)
        finish_reason = _response_finish_reason(response)
        if finish_reason is not None:
            audit["finish_reason"] = finish_reason
            detail["finish_reason"] = finish_reason
    except Exception as exc:
        raise ProviderRunError(
            str(exc),
            audit,
            input_tokens,
            output_tokens,
            usage_details,
            retryable=_is_retryable_provider_error(exc),
        ) from exc
    return ProviderResult(
        text=text,
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        audit=audit,
        usage_details=usage_details,
    )


def _load_copilot_sdk() -> tuple[type, type, type]:
    try:
        from copilot import CopilotClient
        from copilot.session_events import AssistantMessageData, AssistantUsageData
    except ImportError as exc:
        raise RuntimeError("github-copilot-sdk is not installed") from exc
    return CopilotClient, AssistantMessageData, AssistantUsageData


def _copilot_token() -> str:
    for key in _COPILOT_TOKEN_KEYS:
        token = os.environ.get(key)
        if token:
            return token
    raise RuntimeError("COPILOT_GITHUB_TOKEN, GH_TOKEN, or GITHUB_TOKEN is required")


@dataclass(frozen=True)
class _CopilotUsageSnapshot:
    input_tokens: int | None = None
    output_tokens: int | None = None
    finish_reason: str | None = None
    details: tuple[dict[str, object], ...] = ()


def _copilot_usage(events: list[object], usage_data_type: type | None) -> _CopilotUsageSnapshot:
    input_values: list[int] = []
    output_values: list[int] = []
    finish_reason: str | None = None
    details: list[dict[str, object]] = []
    if usage_data_type is None:
        return _CopilotUsageSnapshot()

    try:
        runtime_version = importlib.metadata.version("github-copilot-sdk")
    except importlib.metadata.PackageNotFoundError:
        runtime_version = None

    for event in events:
        data = getattr(event, "data", None)
        if not isinstance(data, usage_data_type):
            continue
        request_input = _optional_nonnegative_int(getattr(data, "input_tokens", None))
        request_output = _optional_nonnegative_int(getattr(data, "output_tokens", None))
        if request_input is not None:
            input_values.append(request_input)
        if request_output is not None:
            output_values.append(request_output)
        event_finish_reason = getattr(data, "finish_reason", None)
        if isinstance(event_finish_reason, str) and event_finish_reason:
            finish_reason = event_finish_reason

        detail: dict[str, object] = {"source": "github_copilot_sdk"}
        optional_values: dict[str, object | None] = {
            "input_tokens": request_input,
            "output_tokens": request_output,
            "cache_read_input_tokens": _optional_nonnegative_int(getattr(data, "cache_read_tokens", None)),
            "cache_write_input_tokens": _optional_nonnegative_int(getattr(data, "cache_write_tokens", None)),
            "reasoning_output_tokens": _optional_nonnegative_int(getattr(data, "reasoning_tokens", None)),
            "model": _enum_value(getattr(data, "model", None)),
            "endpoint": _enum_value(getattr(data, "api_endpoint", None)),
            "duration_secs": _duration_secs(getattr(data, "duration", None)),
            "finish_reason": event_finish_reason if isinstance(event_finish_reason, str) else None,
            "request_id": _enum_value(getattr(data, "api_call_id", None)),
            "provider_request_id": _enum_value(getattr(data, "provider_call_id", None)),
            "runtime_version": runtime_version,
        }
        detail.update({key: value for key, value in optional_values.items() if value is not None})

        costs: list[dict[str, object]] = []
        model_multiplier = _optional_nonnegative_float(getattr(data, "cost", None))
        if model_multiplier is not None:
            costs.append(
                {
                    "amount": model_multiplier,
                    "unit": "model_multiplier",
                    "source": "assistant.usage.cost",
                }
            )
        copilot_usage = getattr(data, "copilot_usage", None)
        nano_aiu = _optional_nonnegative_float(getattr(copilot_usage, "total_nano_aiu", None))
        if nano_aiu is not None:
            costs.append(
                {
                    "amount": nano_aiu,
                    "unit": "nano_aiu",
                    "source": "assistant.usage.copilot_usage.total_nano_aiu",
                }
            )
        if costs:
            detail["costs"] = costs
        details.append(detail)
    return _CopilotUsageSnapshot(
        sum(input_values) if input_values else None,
        sum(output_values) if output_values else None,
        finish_reason,
        tuple(details),
    )


async def _send_copilot_and_wait(
    session: object,
    prompt: str,
    deadline: float | None,
    on_deadline: Callable[[], None] | None = None,
) -> object:
    """Wait for Copilot with a distinguishable runner-owned deadline."""

    async def send() -> object:
        return await session.send_and_wait(  # type: ignore[attr-defined]
            prompt,
            agent_mode="interactive",
            timeout=None,
        )

    if deadline is None:
        return await send()

    remaining = deadline - time.time()
    if remaining <= 0:
        if on_deadline is not None:
            on_deadline()
        raise _CopilotDeadlineExceeded

    task = asyncio.create_task(send())
    try:
        done, _pending = await asyncio.wait({task}, timeout=remaining)
    except asyncio.CancelledError:
        task.cancel()
        raise
    if task in done:
        # A provider/network TimeoutError raised by the task remains a normal
        # provider failure; only our own elapsed deadline gets the marker below.
        return task.result()

    task.cancel()
    # Emit the terminal timeout evidence before any cancellation wait or SDK
    # context teardown can hang. The host gives this flush a bounded grace and
    # hard-kills only after that grace expires.
    if on_deadline is not None:
        on_deadline()
    raise _CopilotDeadlineExceeded


async def run_copilot(
    prompt: str,
    model: str,
    workspace: str,
    deadline: float | None,
    handler: StrictCopilotRequestHandler | None = None,
    on_timeout: Callable[[ProviderTimeoutError], None] | None = None,
    reasoning_effort: str | None = None,
    max_output_tokens: int | None = None,
    on_response: Callable[[str], None] | None = None,
    on_model_output: Callable[[str], None] | None = None,
) -> ProviderResult:
    guard = handler or StrictCopilotRequestHandler(
        prompt,
        model,
        reasoning_effort,
        max_output_tokens,
    )
    if handler is not None and max_output_tokens != handler.requested_max_output_tokens:
        raise ValueError("handler output token limit does not match run_copilot")
    guard.model = model
    guard.reasoning_effort = reasoning_effort
    guard.set_deadline(deadline)
    events: list[object] = []
    usage_data_type: type | None = None
    session: object | None = None
    deadline_reported = False
    model_output_observed = False
    text: str | None = None
    owner_task = asyncio.current_task()
    abort_tasks: set[asyncio.Task[None]] = set()

    def observe_model_output(kind: str, *, persist: bool = True) -> None:
        nonlocal model_output_observed
        if model_output_observed:
            return
        model_output_observed = True
        if persist and on_model_output is not None:
            on_model_output(kind)

    def timeout_error() -> ProviderTimeoutError:
        usage = _copilot_usage(events, usage_data_type)
        audit = guard.audit()
        if usage.finish_reason is not None:
            audit["finish_reason"] = usage.finish_reason
        return ProviderTimeoutError(
            "Copilot request reached benchmark deadline",
            audit,
            usage.input_tokens,
            usage.output_tokens,
            usage.details,
        )

    async def abort_session(target: object) -> None:
        try:
            await target.abort()  # type: ignore[attr-defined]
        except Exception:
            # The guard is already frozen. Abort is only a best-effort signal to
            # stop provider work and must never delay or replace durable evidence.
            return

    def schedule_abort() -> None:
        if session is None:
            return
        task = asyncio.create_task(abort_session(session))
        abort_tasks.add(task)
        task.add_done_callback(abort_tasks.discard)

    def report_deadline() -> None:
        nonlocal deadline_reported
        if deadline_reported:
            return
        deadline_reported = True
        # Freeze first so the bounded drain window cannot start another model
        # request. Persist the stable audit before any SDK abort/teardown await.
        guard.freeze()
        error = timeout_error()
        try:
            if on_timeout is not None:
                on_timeout(error)
        finally:
            schedule_abort()

    async def deadline_watchdog() -> None:
        assert deadline is not None
        remaining = deadline - time.time()
        if remaining > 0:
            await asyncio.sleep(remaining)
        report_deadline()
        if owner_task is not None and not owner_task.done():
            owner_task.cancel()

    if deadline is not None and deadline <= time.time():
        report_deadline()
        raise timeout_error()
    watchdog_task = asyncio.create_task(deadline_watchdog()) if deadline is not None else None

    try:
        CopilotClient, AssistantMessageData, AssistantUsageData = _load_copilot_sdk()
        usage_data_type = AssistantUsageData
        token = _copilot_token()
        reasoning_options = {"reasoning_effort": reasoning_effort} if reasoning_effort is not None else {}

        def record_event(event: object) -> None:
            nonlocal text
            events.append(event)
            event_retryability = _copilot_event_error_retryability([event])
            if _enum_value(_get(event, "type")) in {"session.error", "model.call_failure"}:
                guard.record_event_failure(event, event_retryability)
            data = getattr(event, "data", None)
            output_kind = _copilot_event_model_output_kind(event)
            if output_kind is not None:
                observe_model_output(output_kind)
            if isinstance(data, AssistantUsageData) and (
                _nonnegative_int(getattr(data, "output_tokens", None)) > 0
                or _nonnegative_int(getattr(data, "reasoning_tokens", None)) > 0
            ):
                observe_model_output("assistant.usage")
            if not isinstance(data, AssistantMessageData):
                return
            candidate = getattr(data, "content", None)
            valid_response = (
                isinstance(candidate, str) and bool(candidate.strip()) and not getattr(data, "tool_requests", None)
            )
            observe_model_output("assistant.message", persist=not valid_response)
            if not valid_response:
                return
            if text is not None and text != candidate:
                raise RuntimeError("Copilot returned conflicting final assistant messages")
            if text is None:
                text = candidate
                guard.seal_after_response()
                if on_response is not None:
                    on_response(candidate)

        with tempfile.TemporaryDirectory(prefix="tlaps-bench-copilot-") as base_directory:
            async with CopilotClient(
                github_token=token,
                use_logged_in_user=False,
                base_directory=base_directory,
                working_directory=workspace,
                mode="empty",
                request_handler=guard,
                log_level="none",
            ) as client:
                session = await client.create_session(
                    model=model,
                    tools=[],
                    available_tools=[],
                    system_message={"mode": "replace", "content": ""},
                    tool_search={"enabled": False},
                    capi={"enable_web_socket_responses": False},
                    enable_session_telemetry=False,
                    skip_custom_instructions=True,
                    streaming=True,
                    include_sub_agent_streaming_events=False,
                    mcp_servers={},
                    custom_agents=[],
                    enable_config_discovery=False,
                    skip_embedding_retrieval=True,
                    enable_on_demand_instruction_discovery=False,
                    enable_file_hooks=False,
                    enable_host_git_operations=False,
                    enable_session_store=False,
                    enable_skills=False,
                    plugin_directories=[],
                    instruction_directories=[],
                    infinite_sessions={"enabled": False},
                    memory={"enabled": False},
                    on_event=record_event,
                    **reasoning_options,
                )
                if deadline_reported:
                    schedule_abort()
                    raise _CopilotDeadlineExceeded
                guard.bind_session(session.session_id)
                async with session:
                    guard.begin_agent_turn()
                    final_event = await _send_copilot_and_wait(session, prompt, deadline, report_deadline)
                    if final_event is None or not isinstance(final_event.data, AssistantMessageData):
                        raise RuntimeError("Copilot returned no final assistant message")
                    final_text = final_event.data.content
                    valid_response = (
                        isinstance(final_text, str)
                        and bool(final_text.strip())
                        and not getattr(final_event.data, "tool_requests", None)
                    )
                    observe_model_output("assistant.message", persist=not valid_response)
                    if not isinstance(final_text, str) or not final_text.strip():
                        raise RuntimeError("Copilot returned an empty assistant message")
                    if getattr(final_event.data, "tool_requests", None):
                        raise RuntimeError("Copilot returned tool requests in strict one-shot mode")
                    if text is not None and text != final_text:
                        raise RuntimeError("Copilot returned conflicting final assistant messages")
                    if text is None:
                        text = final_text
                        guard.seal_after_response()
                        if on_response is not None:
                            on_response(final_text)

        guard.assert_complete()
    except asyncio.CancelledError as exc:
        if deadline_reported:
            raise timeout_error() from exc
        raise
    except Exception as exc:
        usage = _copilot_usage(events, usage_data_type)
        audit = guard.audit()
        if usage.finish_reason is not None:
            audit["finish_reason"] = usage.finish_reason
        deadline_closed = audit.get("deadline_closed") is True
        if (
            deadline_reported
            or (deadline is not None and isinstance(exc, _CopilotDeadlineExceeded))
            or (deadline is not None and deadline_closed and time.time() >= deadline)
        ):
            raise timeout_error() from exc
        blocked_requests = _nonnegative_int(audit.get("blocked_requests"))
        inference_requests = _nonnegative_int(audit.get("inference_requests"))
        clean_contract = audit.get("contract_ok") is True and blocked_requests == 0 and not deadline_closed
        current_retryability = _provider_error_retryability(exc)
        inference_retryability = _recorded_provider_retryability(
            guard._inference_status_code,
            guard._inference_failure_retryable,
        )
        aux_retryability = _recorded_provider_retryability(
            guard._aux_status_code,
            guard._aux_failure_retryable,
        )
        event_retryability = _copilot_event_error_retryability(events)
        if (
            _exception_status_code(exc) == 400
            and event_retryability is True
            and _copilot_bodyless_bad_request_observed(events)
        ):
            current_retryability = True
        permanent_evidence = (
            current_retryability is False
            or event_retryability is False
            or (inference_requests > 0 and inference_retryability is False)
            or (guard._last_forward_kind == "aux" and aux_retryability is False)
        )
        provider_transient = not permanent_evidence and (
            current_retryability is True
            or event_retryability is True
            or inference_retryability is True
            or (guard._last_forward_kind == "aux" and aux_retryability is True)
        )
        retryable = not model_output_observed and provider_transient and clean_contract
        error_message = str(exc)
        permanent_guard_marker = "strict one-shot: blocked inference retry after a permanent provider error"
        if permanent_guard_marker in error_message:
            error_message = guard.permanent_failure_message() or error_message
        raise ProviderRunError(
            error_message,
            audit,
            usage.input_tokens,
            usage.output_tokens,
            usage.details,
            retryable=retryable,
        ) from exc
    finally:
        if watchdog_task is not None:
            watchdog_task.cancel()

    usage = _copilot_usage(events, usage_data_type)
    audit = guard.audit()
    if usage.finish_reason is not None:
        audit["finish_reason"] = usage.finish_reason
    assert text is not None
    return ProviderResult(text, usage.input_tokens, usage.output_tokens, audit, usage.details)


class OneShotProvider(Protocol):
    """Runtime adapter used by the provider-neutral one-shot process."""

    @property
    def audit(self) -> dict[str, object]: ...

    def invoke(self, on_timeout: Callable[[ProviderTimeoutError], None]) -> ProviderResult: ...


ProviderFactory = Callable[..., OneShotProvider]


class _LiteLLMProvider:
    def __init__(
        self,
        prompt: str,
        model: str,
        _workspace: str,
        _deadline: float | None,
        reasoning_effort: str | None = None,
    ) -> None:
        self.prompt = prompt
        self.model = model
        self.reasoning_effort = reasoning_effort

    @property
    def audit(self) -> dict[str, object]:
        return _litellm_audit(self.prompt, self.model, reasoning_effort=self.reasoning_effort)

    def invoke(self, _on_timeout: Callable[[ProviderTimeoutError], None]) -> ProviderResult:
        if self.reasoning_effort is None:
            return run_litellm(self.prompt, self.model)
        return run_litellm(self.prompt, self.model, self.reasoning_effort)


class _CopilotProvider:
    def __init__(
        self,
        prompt: str,
        model: str,
        workspace: str,
        deadline: float | None,
        reasoning_effort: str | None = None,
        max_output_tokens: int | None = None,
    ) -> None:
        self.prompt = prompt
        self.model = model
        self.workspace = workspace
        self.deadline = deadline
        self.reasoning_effort = reasoning_effort
        self.max_output_tokens = max_output_tokens
        self.guard = StrictCopilotRequestHandler(prompt, model, reasoning_effort, max_output_tokens)
        self.on_response: Callable[[str], None] | None = None
        self.on_model_output: Callable[[str], None] | None = None

    @property
    def audit(self) -> dict[str, object]:
        return self.guard.audit()

    def set_output_callbacks(
        self,
        on_response: Callable[[str], None],
        on_model_output: Callable[[str], None],
    ) -> None:
        self.on_response = on_response
        self.on_model_output = on_model_output

    def invoke(self, on_timeout: Callable[[ProviderTimeoutError], None]) -> ProviderResult:
        run_options: dict[str, Any] = {}
        if self.reasoning_effort is not None:
            run_options["reasoning_effort"] = self.reasoning_effort
        if self.max_output_tokens is not None:
            run_options["max_output_tokens"] = self.max_output_tokens
        return asyncio.run(
            run_copilot(
                self.prompt,
                self.model,
                self.workspace,
                self.deadline,
                handler=self.guard,
                on_timeout=on_timeout,
                on_response=self.on_response,
                on_model_output=self.on_model_output,
                **run_options,
            )
        )


_PROVIDER_REGISTRY: dict[str, ProviderFactory] = {
    "litellm": _LiteLLMProvider,
    "copilot": _CopilotProvider,
}


def register_provider(name: str, factory: ProviderFactory) -> None:
    """Register a one-shot provider without changing the runner lifecycle."""

    if not name or name in _PROVIDER_REGISTRY:
        raise ValueError(f"one-shot provider already registered or invalid: {name!r}")
    _PROVIDER_REGISTRY[name] = factory


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run one strict one-shot agent turn")
    parser.add_argument("--provider", required=True, choices=sorted(_PROVIDER_REGISTRY))
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--result-dir", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--deadline", type=float, default=0.0)
    args = parser.parse_args(argv)
    if args.max_output_tokens is not None:
        if args.max_output_tokens <= 0:
            parser.error("--max-output-tokens must be > 0")
        if args.provider != "copilot":
            parser.error("--max-output-tokens is only supported for provider copilot")
    return args


def _emit_usage_events(
    *,
    provider: str,
    input_tokens: int | None,
    output_tokens: int | None,
    model_requests: int,
    usage_details: tuple[dict[str, object], ...],
    complete: bool,
    is_lower_bound: bool,
) -> None:
    """Emit one normalized usage event per captured model request."""

    if usage_details:
        if len(usage_details) > model_requests:
            for _request in range(model_requests):
                _emit(
                    "usage",
                    model_requests=1,
                    source=f"{provider}_oneshot_runner",
                    complete=False,
                    is_lower_bound=True,
                    usage_unavailable=True,
                    usage_record_mismatch=True,
                )
            return
        for detail in usage_details:
            payload = {
                "model_requests": 1,
                "source": f"{provider}_oneshot_runner",
                "complete": complete,
                "is_lower_bound": is_lower_bound,
                **detail,
            }
            _emit("usage", **payload)
        for _missing_request in range(max(model_requests - len(usage_details), 0)):
            _emit(
                "usage",
                model_requests=1,
                source=f"{provider}_oneshot_runner",
                complete=False,
                is_lower_bound=True,
                usage_unavailable=True,
            )
        return

    if model_requests > 1 and input_tokens is None and output_tokens is None:
        for _missing_request in range(model_requests):
            _emit(
                "usage",
                model_requests=1,
                source=f"{provider}_oneshot_runner",
                complete=False,
                is_lower_bound=True,
                usage_unavailable=True,
            )
        return

    payload: dict[str, object] = {
        "model_requests": model_requests,
        "source": f"{provider}_oneshot_runner",
        "complete": complete,
        "is_lower_bound": is_lower_bound,
    }
    if input_tokens is not None:
        payload["input_tokens"] = input_tokens
    if output_tokens is not None:
        payload["output_tokens"] = output_tokens
    _emit("usage", **payload)


def _usage_details_complete(usage_details: tuple[dict[str, object], ...], model_requests: int) -> bool:
    """Return whether every model request has explicit core token counts."""

    return (
        model_requests > 0
        and len(usage_details) == model_requests
        and all(
            _optional_nonnegative_int(detail.get("input_tokens")) is not None
            and _optional_nonnegative_int(detail.get("output_tokens")) is not None
            for detail in usage_details
        )
    )


def _usage_complete(
    input_tokens: int | None,
    output_tokens: int | None,
    usage_details: tuple[dict[str, object], ...],
    model_requests: int,
) -> bool:
    """Accept explicit aggregate counts or complete per-request evidence."""

    if usage_details:
        return _usage_details_complete(usage_details, model_requests)
    return (
        model_requests > 0
        and _optional_nonnegative_int(input_tokens) is not None
        and _optional_nonnegative_int(output_tokens) is not None
    )


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    prompt = sys.stdin.read()
    if not prompt.strip():
        _emit("error", message="empty prompt on stdin")
        _emit("result", status="error", model_requests=0)
        return 1
    deadline = args.deadline if args.deadline > 0 else None
    factory = _PROVIDER_REGISTRY[args.provider]
    provider_options: dict[str, object] = {}
    if args.reasoning_effort is not None:
        provider_options["reasoning_effort"] = args.reasoning_effort
    if args.max_output_tokens is not None:
        provider_options["max_output_tokens"] = args.max_output_tokens
    provider = factory(prompt, args.model, args.workspace, deadline, **provider_options)
    terminal_emitted = False
    response_emitted = False
    model_output_emitted = False

    def emit_model_output(kind: str) -> None:
        nonlocal model_output_emitted
        if terminal_emitted or model_output_emitted:
            return
        _emit("model_output_observed", kind=kind, model_requests=1)
        model_output_emitted = True

    def emit_response(text: str) -> None:
        nonlocal response_emitted
        if terminal_emitted or response_emitted:
            return
        emit_model_output("response")
        _emit("response", text=text)
        response_emitted = True

    callback_setter = getattr(provider, "set_output_callbacks", None)
    if callable(callback_setter):
        callback_setter(emit_response, emit_model_output)

    def emit_failure(exc: Exception) -> None:
        nonlocal terminal_emitted
        if terminal_emitted:
            return
        terminal_emitted = True
        audit = provider.audit
        input_tokens: int | None = None
        output_tokens: int | None = None
        usage_details: tuple[dict[str, object], ...] = ()
        if isinstance(exc, ProviderRunError):
            audit = exc.audit
            input_tokens = exc.input_tokens
            output_tokens = exc.output_tokens
            usage_details = exc.usage_details
        request_count = audit.get(
            "model_requests",
            audit.get("litellm_completion_invocations", audit.get("inference_requests", 0)),
        )
        model_requests = _nonnegative_int(request_count)
        if model_requests > 0:
            usage_complete = _usage_details_complete(usage_details, model_requests)
            _emit_usage_events(
                provider=args.provider,
                input_tokens=input_tokens,
                output_tokens=output_tokens,
                model_requests=model_requests,
                usage_details=usage_details,
                complete=usage_complete,
                is_lower_bound=not usage_complete,
            )
        _emit("request_audit", **audit)
        _emit("error", message=str(exc))
        status = "timeout" if isinstance(exc, ProviderTimeoutError) else "error"
        result: dict[str, object] = {"status": status, "model_requests": model_requests}
        if status == "error":
            result["retryable"] = isinstance(exc, ProviderRunError) and exc.retryable
        _emit("result", **result)

    try:
        result = provider.invoke(emit_failure)
        if terminal_emitted:
            return 1
        emit_response(result.text)
        request_count = result.audit.get(
            "model_requests",
            result.audit.get(
                "litellm_completion_invocations",
                result.audit.get("inference_requests", 0),
            ),
        )
        model_requests = _nonnegative_int(request_count)
        usage_complete = _usage_complete(
            result.input_tokens,
            result.output_tokens,
            result.usage_details,
            model_requests,
        )
        _emit_usage_events(
            provider=args.provider,
            input_tokens=result.input_tokens,
            output_tokens=result.output_tokens,
            model_requests=model_requests,
            usage_details=result.usage_details,
            complete=usage_complete,
            is_lower_bound=not usage_complete,
        )
        _emit("request_audit", **result.audit)
        _emit("result", status="success", model_requests=model_requests)
        return 0
    except Exception as exc:
        emit_failure(exc)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
