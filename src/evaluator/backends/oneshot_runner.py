"""Provider-neutral strict one-shot model runner.

The process reads one prompt from stdin and writes JSONL events to stdout.  The
LiteLLM path makes one completion call with retries disabled.  The Copilot path
uses the official SDK's request-handler seam to remove SDK-added context at the
wire boundary and fail closed before a second inference request is forwarded.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import os
import sys
import tempfile
from dataclasses import dataclass
from typing import Any
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


def _emit(event_type: str, **payload: object) -> None:
    print(json.dumps({"type": event_type, **payload}, ensure_ascii=False), flush=True)


def _nonnegative_int(value: object) -> int:
    if isinstance(value, bool):
        return 0
    try:
        return max(int(value), 0)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return 0


def _get(value: object, name: str, default: object = None) -> object:
    if isinstance(value, dict):
        return value.get(name, default)
    return getattr(value, name, default)


def _inference_endpoint(url: str) -> str | None:
    path = urlsplit(url).path.lower().rstrip("/")
    for endpoint in _INFERENCE_ENDPOINTS:
        if path.endswith(endpoint):
            return endpoint
    return None


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


class StrictCopilotRequestHandler(_CopilotRequestHandler):
    """Rewrite the sole Copilot inference request and block every later attempt."""

    def __init__(self, prompt: str, model: str | None = None) -> None:
        self._prompt = prompt
        self.model = model
        self._expected_session_id: str | None = None
        self.inference_attempts = 0
        self.forwarded_inference_requests = 0
        self.blocked_requests = 0
        self.unknown_requests = 0
        self.endpoint: str | None = None
        self.request_sha256: str | None = None
        self.system_removed = False
        self.tools_removed = False

    def bind_session(self, session_id: str) -> None:
        if not session_id:
            raise RuntimeError("strict one-shot: Copilot session has no id")
        if self._expected_session_id is not None and self._expected_session_id != session_id:
            raise RuntimeError("strict one-shot: handler cannot be rebound to another session")
        self._expected_session_id = session_id

    async def _forward(self, request: httpx.Request, ctx: object) -> httpx.Response:
        return await super().send_request(request, ctx)

    async def send_request(self, request: httpx.Request, ctx: object) -> httpx.Response:
        endpoint = _inference_endpoint(str(request.url))
        if endpoint is None:
            if _auxiliary_endpoint(str(request.url)) is not None:
                return await self._forward(request, ctx)
            self.blocked_requests += 1
            self.unknown_requests += 1
            raise RuntimeError("strict one-shot: blocked unknown model-layer endpoint")

        self.inference_attempts += 1
        self.endpoint = endpoint
        session_id = getattr(ctx, "session_id", None)
        if self._expected_session_id is None or session_id != self._expected_session_id:
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: inference request has an unexpected session id")
        if self.forwarded_inference_requests != 0:
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: blocked inference request after the first")
        if request.method.upper() != "POST":
            self.blocked_requests += 1
            raise RuntimeError("strict one-shot: inference request must use POST")

        try:
            payload = json.loads(request.content)
            rewritten_payload = _rewrite_inference_payload(endpoint, payload, self._prompt)
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

        headers = [
            (name, value)
            for name, value in request.headers.multi_items()
            if name.lower() not in _FORBIDDEN_FORWARD_HEADERS
        ]
        rewritten = httpx.Request(request.method, request.url, headers=headers, content=body)

        # Reserve the only forwarding slot before the await.  A runtime retry or
        # concurrent attempt therefore observes the slot as consumed even when
        # the first upstream request fails after being sent.
        self.forwarded_inference_requests = 1
        self.request_sha256 = hashlib.sha256(body).hexdigest()
        self.system_removed = True
        self.tools_removed = True
        return await self._forward(rewritten, ctx)

    async def open_websocket(self, _ctx: object) -> object:
        self.inference_attempts += 1
        self.blocked_requests += 1
        raise RuntimeError("strict one-shot: WebSocket inference is disabled")

    def assert_complete(self) -> None:
        if self.inference_attempts != 1 or self.forwarded_inference_requests != 1 or self.blocked_requests != 0:
            raise RuntimeError("strict one-shot: expected exactly one inference attempt and one forwarded request")

    def audit(self) -> dict[str, object]:
        audit: dict[str, object] = {
            "provider": "copilot",
            "wire_audited": True,
            "inference_requests": self.forwarded_inference_requests,
            "inference_attempts": self.inference_attempts,
            "blocked_requests": self.blocked_requests,
            "unknown_requests": self.unknown_requests,
            "system_removed": self.system_removed,
            "tools_removed": self.tools_removed,
        }
        if self.model is not None:
            audit["model"] = self.model
        if self.endpoint is not None:
            audit["endpoint"] = self.endpoint
        if self.request_sha256 is not None:
            audit["request_sha256"] = self.request_sha256
        return audit


@dataclass(frozen=True)
class ProviderResult:
    text: str
    input_tokens: int
    output_tokens: int
    audit: dict[str, object]


class ProviderRunError(RuntimeError):
    """Provider failure carrying the request audit accumulated before it failed."""

    def __init__(self, message: str, audit: dict[str, object]) -> None:
        super().__init__(message)
        self.audit = audit


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


def run_litellm(prompt: str, model: str) -> ProviderResult:
    request = {"model": model, "messages": [{"role": "user", "content": prompt}]}
    request_sha256 = hashlib.sha256(
        json.dumps(request, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    audit: dict[str, object] = {
        "provider": "litellm",
        "model": model,
        "litellm_completion_invocations": 0,
        "wire_audited": False,
        "litellm_retries_disabled": True,
        "request_sha256": request_sha256,
        "system_supplied": False,
        "tools_supplied": False,
        "max_tokens": 32_768,
    }
    try:
        import litellm
    except ImportError as exc:
        raise ProviderRunError("litellm is not installed", audit) from exc

    max_tokens = _litellm_max_tokens(litellm, model)
    audit["max_tokens"] = max_tokens

    # This disables LiteLLM's own retry orchestration. Provider transports may
    # have behavior below this adapter boundary, so this is intentionally not
    # described as a wire-level request count.
    try:
        audit["litellm_completion_invocations"] = 1
        response = litellm.completion(
            model=model,
            messages=request["messages"],
            stream=False,
            temperature=0.0,
            max_tokens=max_tokens,
            num_retries=0,
        )
        usage = _get(response, "usage", {})
        input_tokens = _nonnegative_int(_get(usage, "prompt_tokens", _get(usage, "input_tokens", 0)))
        output_tokens = _nonnegative_int(_get(usage, "completion_tokens", _get(usage, "output_tokens", 0)))
        text = _response_text(response)
        finish_reason = _response_finish_reason(response)
        if finish_reason is not None:
            audit["finish_reason"] = finish_reason
    except Exception as exc:
        raise ProviderRunError(str(exc), audit) from exc
    return ProviderResult(
        text=text,
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        audit=audit,
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


async def run_copilot(
    prompt: str,
    model: str,
    workspace: str,
    timeout: float,
    handler: StrictCopilotRequestHandler | None = None,
) -> ProviderResult:
    CopilotClient, AssistantMessageData, AssistantUsageData = _load_copilot_sdk()
    token = _copilot_token()
    guard = handler or StrictCopilotRequestHandler(prompt)
    guard.model = model
    events: list[object] = []

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
                on_event=events.append,
            )
            guard.bind_session(session.session_id)
            async with session:
                final_event = await session.send_and_wait(
                    prompt,
                    agent_mode="interactive",
                    timeout=timeout,
                )

    guard.assert_complete()
    if final_event is None or not isinstance(final_event.data, AssistantMessageData):
        raise RuntimeError("Copilot returned no final assistant message")
    text = final_event.data.content
    if not isinstance(text, str) or not text.strip():
        raise RuntimeError("Copilot returned an empty assistant message")
    if getattr(final_event.data, "tool_requests", None):
        raise RuntimeError("Copilot returned tool requests in strict one-shot mode")

    input_tokens = 0
    output_tokens = 0
    finish_reason: str | None = None
    for event in events:
        data = getattr(event, "data", None)
        if isinstance(data, AssistantUsageData):
            input_tokens += _nonnegative_int(data.input_tokens)
            output_tokens += _nonnegative_int(data.output_tokens)
            event_finish_reason = getattr(data, "finish_reason", None)
            if isinstance(event_finish_reason, str) and event_finish_reason:
                finish_reason = event_finish_reason
    audit = guard.audit()
    if finish_reason is not None:
        audit["finish_reason"] = finish_reason
    return ProviderResult(text, input_tokens, output_tokens, audit)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run one strict one-shot model request")
    parser.add_argument("--provider", required=True, choices=("litellm", "copilot"))
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--result-dir", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--timeout", type=float, default=28_800.0)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    prompt = sys.stdin.read()
    if not prompt.strip():
        _emit("error", message="empty prompt on stdin")
        _emit("result", status="error", model_requests=0)
        return 1
    if args.timeout <= 0:
        _emit("error", message="timeout must be positive")
        _emit("result", status="error", model_requests=0)
        return 1

    guard = StrictCopilotRequestHandler(prompt, args.model) if args.provider == "copilot" else None
    if args.provider == "litellm":
        audit: dict[str, object] = {
            "provider": "litellm",
            "model": args.model,
            "litellm_completion_invocations": 0,
            "wire_audited": False,
            "litellm_retries_disabled": True,
        }
    else:
        audit = guard.audit() if guard is not None else {"provider": "copilot", "model": args.model}
    try:
        if args.provider == "litellm":
            result = run_litellm(prompt, args.model)
        else:
            result = asyncio.run(run_copilot(prompt, args.model, args.workspace, args.timeout, handler=guard))
        audit = result.audit
        _emit("response", text=result.text)
        _emit(
            "usage",
            input_tokens=result.input_tokens,
            output_tokens=result.output_tokens,
            model_requests=1,
        )
        _emit("request_audit", **audit)
        _emit("result", status="success", model_requests=1)
        return 0
    except Exception as exc:
        if guard is not None:
            audit = guard.audit()
        elif isinstance(exc, ProviderRunError):
            audit = exc.audit
        _emit("request_audit", **audit)
        _emit("error", message=str(exc))
        request_count = audit.get(
            "litellm_completion_invocations",
            audit.get("inference_requests", 0),
        )
        _emit("result", status="error", model_requests=_nonnegative_int(request_count))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
