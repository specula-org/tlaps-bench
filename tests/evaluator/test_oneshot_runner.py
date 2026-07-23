"""Unit tests for the provider-neutral strict one-shot runner."""

from __future__ import annotations

import asyncio
import io
import json
import sys
import time
import types
from datetime import timedelta
from types import SimpleNamespace

import httpx
import pytest

from evaluator.backends import oneshot_runner
from evaluator.backends.litellm_oneshot import LiteLLMOneShotBackend


class _RecordingHandler(oneshot_runner.StrictCopilotRequestHandler):
    def __init__(self, prompt: str, **kwargs) -> None:
        super().__init__(prompt, **kwargs)
        self.forwarded: list[httpx.Request] = []

    async def _forward(self, request: httpx.Request, _ctx: object) -> httpx.Response:
        self.forwarded.append(request)
        return httpx.Response(200, request=request, content=b"{}")


def _request(url: str, payload: dict | None = None) -> httpx.Request:
    if payload is None:
        return httpx.Request("GET", url, headers={"authorization": "Bearer secret"})
    return httpx.Request(
        "POST",
        url,
        headers={
            "authorization": "Bearer secret",
            "content-type": "application/json",
            "content-length": "999",
            "content-encoding": "gzip",
        },
        content=json.dumps(payload).encode(),
    )


@pytest.mark.parametrize(
    ("url", "endpoint"),
    [
        ("https://example.test/v1/chat/completions?api-version=1", "/chat/completions"),
        ("https://example.test/models/x/responses", "/responses"),
        ("https://example.test/v1/messages", "/v1/messages"),
        ("https://example.test/messages/", "/messages"),
        ("https://example.test/models", None),
        ("https://example.test/models/session", None),
        ("https://example.test/policy", None),
    ],
)
def test_inference_endpoint_matching(url, endpoint):
    assert oneshot_runner._inference_endpoint(url) == endpoint


@pytest.mark.parametrize(
    ("url", "endpoint"),
    [
        ("https://example.test/models", "/models"),
        ("https://example.test/models/session", "/models/session"),
        ("https://example.test/policy", "/policy"),
        ("https://example.test/unknown", None),
    ],
)
def test_auxiliary_endpoint_matching(url, endpoint):
    assert oneshot_runner._auxiliary_endpoint(url) == endpoint


def test_expired_deadline_never_starts_copilot_inference():
    class Session:
        async def send_and_wait(self, *_args, **_kwargs):
            pytest.fail("an expired benchmark deadline must not start inference")

    deadline_events = []

    async def scenario():
        with pytest.raises(oneshot_runner._CopilotDeadlineExceeded):
            await oneshot_runner._send_copilot_and_wait(
                Session(),
                "EXACT PROMPT",
                time.time() - 1,
                lambda: deadline_events.append("timeout"),
            )

    asyncio.run(scenario())

    assert deadline_events == ["timeout"]


def test_deadline_freezes_guard_before_late_runtime_request():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    deadline = time.time() + 0.01
    handler.set_deadline(deadline)

    class Session:
        runtime_task = None

        async def send_and_wait(self, *_args, **_kwargs):
            async def runtime_work():
                await asyncio.sleep(0.03)
                with pytest.raises(RuntimeError, match="after benchmark deadline"):
                    await handler.send_request(
                        _request(
                            "https://api.githubcopilot.com/responses",
                            {"model": "test-model", "input": [], "stream": True},
                        ),
                        SimpleNamespace(session_id="session-1"),
                    )

            self.runtime_task = asyncio.create_task(runtime_work())
            await asyncio.sleep(60)

    snapshots = []

    async def scenario():
        session = Session()

        def on_deadline():
            handler.freeze()
            snapshots.append(handler.audit())

        with pytest.raises(oneshot_runner._CopilotDeadlineExceeded):
            await oneshot_runner._send_copilot_and_wait(session, "EXACT PROMPT", deadline, on_deadline)
        await session.runtime_task

    asyncio.run(scenario())

    assert snapshots[0]["deadline_closed"] is True
    assert snapshots[0]["model_requests"] == 0
    assert handler.audit()["model_requests"] == 0
    assert handler.audit()["blocked_requests"] == 0
    assert handler.audit()["deadline_blocked_requests"] == 1
    assert handler.forwarded == []


def test_freeze_cancels_full_response_stream_forwarding(monkeypatch):
    started = asyncio.Event()

    class BlockingStream(httpx.AsyncByteStream):
        def __init__(self):
            self.closed = False

        async def __aiter__(self):
            started.set()
            await asyncio.Future()
            yield b""

        async def aclose(self):
            self.closed = True

    stream = BlockingStream()

    async def fake_base_forward_http(self, request, _exchange, ctx):
        response = await self.send_request(request, ctx)
        try:
            async for _chunk in response.aiter_raw():
                pass
        finally:
            await response.aclose()

    class StreamingHandler(oneshot_runner.StrictCopilotRequestHandler):
        async def _forward(self, request, _ctx):
            return httpx.Response(200, request=request, stream=stream)

    monkeypatch.setattr(oneshot_runner._CopilotRequestHandler, "_forward_http", fake_base_forward_http, raising=False)
    handler = StreamingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    request = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )

    async def scenario():
        task = asyncio.create_task(handler._forward_http(request, object(), SimpleNamespace(session_id="session-1")))
        await started.wait()
        assert handler._forward_tasks == {task}

        handler.freeze()

        with pytest.raises(asyncio.CancelledError):
            await task
        assert stream.closed is True
        assert handler._forward_tasks == set()

    asyncio.run(scenario())


def test_response_body_transport_failure_is_retryable_evidence(monkeypatch):
    request = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )

    class FailingStream(httpx.AsyncByteStream):
        def __init__(self):
            self.closed = False

        async def __aiter__(self):
            raise httpx.ReadError("stream reset", request=request)
            yield b""

        async def aclose(self):
            self.closed = True

    stream = FailingStream()

    async def fake_base_forward_http(self, forwarded_request, _exchange, ctx):
        response = await self.send_request(forwarded_request, ctx)
        try:
            async for _chunk in response.aiter_raw():
                pass
        finally:
            await response.aclose()

    class StreamingHandler(oneshot_runner.StrictCopilotRequestHandler):
        async def _forward(self, forwarded_request, _ctx):
            return httpx.Response(200, request=forwarded_request, stream=stream)

    monkeypatch.setattr(oneshot_runner._CopilotRequestHandler, "_forward_http", fake_base_forward_http, raising=False)
    handler = StreamingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()

    async def scenario():
        with pytest.raises(httpx.ReadError, match="stream reset"):
            await handler._forward_http(request, object(), SimpleNamespace(session_id="session-1"))

    asyncio.run(scenario())

    assert stream.closed is True
    assert handler._inference_status_code == 200
    assert handler._inference_failure_retryable is True


def test_unknown_body_failure_does_not_erase_transient_evidence(monkeypatch):
    async def fake_base_forward_http(_self, _request, _exchange, _ctx):
        raise RuntimeError("unknown stream failure")

    monkeypatch.setattr(oneshot_runner._CopilotRequestHandler, "_forward_http", fake_base_forward_http, raising=False)
    handler = oneshot_runner.StrictCopilotRequestHandler("EXACT PROMPT")
    handler._inference_status_code = 503
    handler._inference_failure_retryable = True

    async def scenario():
        with pytest.raises(RuntimeError, match="unknown stream failure"):
            await handler._forward_http(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                object(),
                object(),
            )

    asyncio.run(scenario())

    assert handler._inference_status_code == 503
    assert handler._inference_failure_retryable is True


@pytest.mark.parametrize(
    ("endpoint", "payload", "message_key"),
    [
        (
            "/responses",
            {
                "model": "test-model",
                "instructions": "hidden system text",
                "input": [{"role": "user", "content": "<current_datetime>now</current_datetime>\nPROMPT"}],
                "tools": [{"type": "function", "name": "read_file"}],
                "tool_choice": "auto",
                "previous_response_id": "resp-old",
                "stream": True,
            },
            "input",
        ),
        (
            "/chat/completions",
            {
                "model": "test-model",
                "instructions": "cross-schema hidden instructions",
                "input": [{"role": "user", "content": "cross-schema hidden input"}],
                "messages": [
                    {"role": "system", "content": "hidden"},
                    {"role": "user", "content": "decorated prompt"},
                ],
                "prompt": "cross-schema hidden prompt",
                "context": "cross-schema hidden context",
                "custom_prompt_container": {"text": "unknown hidden context"},
                "tools": [{"type": "function"}],
                "functions": [{"name": "old-style-tool"}],
            },
            "messages",
        ),
        (
            "/v1/messages",
            {
                "model": "test-model",
                "system": "hidden",
                "messages": [{"role": "user", "content": "decorated prompt"}],
                "tools": [{"name": "read_file"}],
                "functions": [{"name": "cross-schema-tool"}],
                "conversation": [{"role": "assistant", "content": "old answer"}],
                "history": ["old prompt"],
            },
            "messages",
        ),
    ],
)
def test_rewrite_replaces_context_with_one_user_prompt(endpoint, payload, message_key):
    rewritten = oneshot_runner._rewrite_inference_payload(endpoint, payload, "EXACT PROMPT")

    assert rewritten["model"] == "test-model"
    assert "hidden" not in json.dumps(rewritten)
    assert "decorated" not in json.dumps(rewritten)
    assert "current_datetime" not in json.dumps(rewritten)
    assert "unknown hidden context" not in json.dumps(rewritten)
    assert "tools" not in rewritten
    assert "tool_choice" not in rewritten
    if message_key == "input":
        assert rewritten[message_key] == [
            {
                "role": "user",
                "content": [{"type": "input_text", "text": "EXACT PROMPT"}],
                "type": "message",
            }
        ]
    else:
        assert rewritten[message_key] == [{"role": "user", "content": "EXACT PROMPT"}]


def test_rewrite_fails_closed_on_nested_hidden_context_in_retained_control_field():
    with pytest.raises(RuntimeError, match="retained hidden context field history"):
        oneshot_runner._rewrite_inference_payload(
            "/responses",
            {"model": "test-model", "reasoning": {"history": ["old prompt"]}},
            "EXACT PROMPT",
        )


def test_copilot_handler_rewrites_each_same_turn_inference_attempt():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    ctx = SimpleNamespace(session_id="session-1")
    original = _request(
        "https://api.githubcopilot.com/responses",
        {
            "model": "test-model",
            "instructions": "SDK system prompt",
            "input": [{"role": "user", "content": "SDK-added context\nEXACT PROMPT"}],
            "tools": [{"type": "function", "name": "shell"}],
            "stream": True,
        },
    )

    asyncio.run(handler.send_request(original, ctx))

    assert len(handler.forwarded) == 1
    forwarded = handler.forwarded[0]
    body = json.loads(forwarded.content)
    assert body["input"] == [
        {
            "role": "user",
            "content": [{"type": "input_text", "text": "EXACT PROMPT"}],
            "type": "message",
        }
    ]
    assert "instructions" not in body
    assert "tools" not in body
    assert forwarded.headers["authorization"] == "Bearer secret"
    assert "content-encoding" not in forwarded.headers
    assert forwarded.headers["content-length"] == str(len(forwarded.content))
    assert handler.audit() == {
        "provider": "copilot",
        "model_requests": 1,
        "request_attempts": 1,
        "system_prompt_present": False,
        "tools_present": False,
        "retries_enabled": True,
        "retry_scope": "incomplete_response",
        "max_inference_attempts": 6,
        "logical_agent_turns": 1,
        "completed_responses": 0,
        "audit_scope": "wire",
        "contract_ok": True,
        "wire_audited": True,
        "inference_requests": 1,
        "inference_attempts": 1,
        "blocked_requests": 0,
        "deadline_blocked_requests": 0,
        "unknown_requests": 0,
        "system_removed": True,
        "tools_removed": True,
        "deadline_closed": False,
        "inference_request_details": [
            {
                "attempt": 1,
                "endpoint": "/responses",
                "request_url_sha256": handler.request_url_sha256,
                "request_sha256": handler.request_sha256,
                "stream_completed": False,
                "status_code": 200,
            }
        ],
        "endpoint": "/responses",
        "request_url_sha256": handler.request_url_sha256,
        "request_sha256": handler.request_sha256,
    }
    assert "secret" not in json.dumps(handler.audit())
    assert "EXACT PROMPT" not in json.dumps(handler.audit())

    asyncio.run(handler.send_request(original, ctx))
    assert len(handler.forwarded) == 2
    assert handler.forwarded[0].content == handler.forwarded[1].content
    assert handler.inference_attempts == 2
    assert handler.blocked_requests == 0


def test_copilot_handler_blocks_retry_after_permanent_status():
    class PermanentHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            return httpx.Response(401, request=request)

    handler = PermanentHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    request = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )
    ctx = SimpleNamespace(session_id="session-1")

    asyncio.run(handler.send_request(request, ctx))
    with pytest.raises(RuntimeError, match="permanent provider error"):
        asyncio.run(handler.send_request(request, ctx))

    assert len(handler.forwarded) == 1
    assert handler.permanent_failure_message() == "HTTP 401"
    assert handler.audit()["inference_requests"] == 1
    assert handler.audit()["inference_attempts"] == 2
    assert handler.audit()["blocked_requests"] == 1


def test_permanent_stream_failure_stays_sticky_and_guard_error_is_not_reassigned(monkeypatch):
    request = _request(
        "https://api.githubcopilot.com/v1/messages",
        {"model": "test-model", "max_tokens": 64_000, "messages": [], "stream": True},
    )

    class FailingStream(httpx.AsyncByteStream):
        async def __aiter__(self):
            raise httpx.ReadError("late stream reset", request=request)
            yield b""

        async def aclose(self):
            return None

    async def fake_base_forward_http(self, forwarded_request, _exchange, ctx):
        response = await self.send_request(forwarded_request, ctx)
        try:
            async for _chunk in response.aiter_raw():
                pass
        finally:
            await response.aclose()

    class PermanentStreamingHandler(oneshot_runner.StrictCopilotRequestHandler):
        def __init__(self, prompt):
            super().__init__(prompt)
            self.forwarded = []

        async def _forward(self, forwarded_request, _ctx):
            self.forwarded.append(forwarded_request)
            return httpx.Response(401, request=forwarded_request, stream=FailingStream())

    monkeypatch.setattr(
        oneshot_runner._CopilotRequestHandler,
        "_forward_http",
        fake_base_forward_http,
        raising=False,
    )
    handler = PermanentStreamingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    ctx = SimpleNamespace(session_id="session-1")

    async def scenario():
        with pytest.raises(httpx.ReadError, match="late stream reset"):
            await handler._forward_http(request, object(), ctx)
        handler.record_event_failure(
            SimpleNamespace(
                type="model.call_failure",
                data=SimpleNamespace(status_code=401, error_message="invalid credentials"),
            ),
            False,
        )
        with pytest.raises(RuntimeError, match="permanent provider error"):
            await handler._forward_http(request, object(), ctx)

    asyncio.run(scenario())

    assert len(handler.forwarded) == 1
    detail = handler.audit()["inference_request_details"][0]
    assert detail["status_code"] == 401
    assert detail["retryable"] is False
    assert detail["error"] == "invalid credentials"
    assert "error_type" not in detail
    assert handler.permanent_failure_message() == "invalid credentials"


def test_copilot_handler_caps_same_turn_inference_attempts():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    request = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )
    ctx = SimpleNamespace(session_id="session-1")

    for _attempt in range(oneshot_runner.COPILOT_MAX_INFERENCE_ATTEMPTS):
        asyncio.run(handler.send_request(request, ctx))
    with pytest.raises(RuntimeError, match="after the retry limit"):
        asyncio.run(handler.send_request(request, ctx))

    assert len(handler.forwarded) == 6
    assert handler.audit()["inference_requests"] == 6
    assert handler.audit()["inference_attempts"] == 7
    assert handler.audit()["blocked_requests"] == 1


@pytest.mark.parametrize("change", ["request", "agent_context", "target_url"])
def test_copilot_handler_blocks_changed_retry(change):
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    first = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )
    first_ctx = SimpleNamespace(
        session_id="session-1",
        agent_id="agent-1",
        parent_agent_id=None,
        interaction_type="user",
    )
    asyncio.run(handler.send_request(first, first_ctx))

    retry = first
    retry_ctx = first_ctx
    if change == "request":
        retry = _request(
            "https://api.githubcopilot.com/responses",
            {"model": "different-model", "input": [], "stream": True},
        )
    elif change == "target_url":
        retry = _request(
            "https://attacker.example/responses",
            {"model": "test-model", "input": [], "stream": True},
        )
    else:
        retry_ctx = SimpleNamespace(
            session_id="session-1",
            agent_id="agent-2",
            parent_agent_id=None,
            interaction_type="user",
        )

    with pytest.raises(RuntimeError, match="changed"):
        asyncio.run(handler.send_request(retry, retry_ctx))

    assert len(handler.forwarded) == 1
    assert handler.audit()["blocked_requests"] == 1
    if change == "target_url":
        assert all(request.url.host == "api.githubcopilot.com" for request in handler.forwarded)


def test_copilot_handler_seals_inference_after_complete_response():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    request = _request(
        "https://api.githubcopilot.com/responses",
        {"model": "test-model", "input": [], "stream": True},
    )
    ctx = SimpleNamespace(session_id="session-1")

    asyncio.run(handler.send_request(request, ctx))
    handler.seal_after_response()
    with pytest.raises(RuntimeError, match="after the complete response"):
        asyncio.run(handler.send_request(request, ctx))

    assert len(handler.forwarded) == 1
    assert handler.audit()["completed_responses"] == 1
    assert handler.audit()["blocked_requests"] == 1


def test_copilot_handler_overrides_runtime_output_limit_on_wire():
    handler = _RecordingHandler("EXACT PROMPT", max_output_tokens=64_000)
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    original = _request(
        "https://api.githubcopilot.com/v1/messages",
        {
            "model": "claude-opus-4.8",
            "max_tokens": 32_000,
            "messages": [{"role": "user", "content": "decorated prompt"}],
            "stream": True,
            "thinking": {"type": "adaptive", "display": "summarized"},
        },
    )

    asyncio.run(handler.send_request(original, SimpleNamespace(session_id="session-1")))

    assert len(handler.forwarded) == 1
    forwarded_body = json.loads(handler.forwarded[0].content)
    assert forwarded_body["max_tokens"] == 64_000
    assert forwarded_body["messages"] == [{"role": "user", "content": "EXACT PROMPT"}]
    assert handler.request_sha256 == oneshot_runner.hashlib.sha256(handler.forwarded[0].content).hexdigest()
    audit = handler.audit()
    assert audit["requested_max_output_tokens"] == 64_000
    assert audit["runtime_max_output_tokens"] == 32_000
    assert audit["wire_max_output_tokens"] == 64_000
    assert audit["contract_ok"] is True
    assert audit["inference_requests"] == 1
    assert audit["inference_attempts"] == 1
    assert audit["blocked_requests"] == 0


def test_copilot_handler_preserves_runtime_output_limit_when_unset():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    original = _request(
        "https://api.githubcopilot.com/v1/messages",
        {
            "model": "claude-opus-4.8",
            "max_tokens": 32_000,
            "messages": [{"role": "user", "content": "decorated prompt"}],
        },
    )

    asyncio.run(handler.send_request(original, SimpleNamespace(session_id="session-1")))

    assert json.loads(handler.forwarded[0].content)["max_tokens"] == 32_000
    audit = handler.audit()
    assert "requested_max_output_tokens" not in audit
    assert audit["runtime_max_output_tokens"] == 32_000
    assert audit["wire_max_output_tokens"] == 32_000


def test_copilot_handler_audits_and_blocks_wrong_session_before_forwarding():
    handler = _RecordingHandler("prompt")
    handler.bind_session("expected-session")
    handler.begin_agent_turn()

    with pytest.raises(RuntimeError, match="unexpected session id"):
        asyncio.run(
            handler.send_request(
                _request("https://api.githubcopilot.com/chat/completions", {"messages": []}),
                SimpleNamespace(session_id="other-session"),
            )
        )

    assert handler.forwarded == []
    assert handler.audit()["inference_attempts"] == 1
    assert handler.audit()["inference_requests"] == 0
    assert handler.audit()["blocked_requests"] == 1
    assert handler.audit()["endpoint"] == "/chat/completions"


def test_copilot_handler_audits_sanitizer_rejection_before_forwarding():
    handler = _RecordingHandler("prompt")
    handler.bind_session("session-1")
    handler.begin_agent_turn()

    with pytest.raises(RuntimeError, match="retained hidden context field history"):
        asyncio.run(
            handler.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "reasoning": {"history": ["old prompt"]}},
                ),
                SimpleNamespace(session_id="session-1"),
            )
        )

    assert handler.forwarded == []
    assert handler.audit()["inference_attempts"] == 1
    assert handler.audit()["inference_requests"] == 0
    assert handler.audit()["blocked_requests"] == 1


def test_copilot_handler_does_not_count_catalog_requests():
    handler = _RecordingHandler("prompt")
    asyncio.run(
        handler.send_request(
            _request("https://api.githubcopilot.com/models"),
            SimpleNamespace(session_id=None),
        )
    )

    assert len(handler.forwarded) == 1
    assert handler.audit()["inference_attempts"] == 0
    assert handler.audit()["inference_requests"] == 0


def test_copilot_handler_blocks_unknown_model_endpoint_before_forwarding():
    handler = _RecordingHandler("prompt")

    with pytest.raises(RuntimeError, match="blocked unknown model-layer endpoint"):
        asyncio.run(
            handler.send_request(
                _request("https://api.githubcopilot.com/future/inference"),
                SimpleNamespace(session_id=None),
            )
        )

    assert handler.forwarded == []
    assert handler.audit()["inference_attempts"] == 0
    assert handler.audit()["inference_requests"] == 0
    assert handler.audit()["unknown_requests"] == 1
    assert handler.audit()["blocked_requests"] == 1


def test_copilot_handler_fails_closed_on_websocket():
    handler = _RecordingHandler("prompt")
    with pytest.raises(RuntimeError, match="WebSocket inference is disabled"):
        asyncio.run(handler.open_websocket(SimpleNamespace(session_id="session-1")))
    assert handler.inference_attempts == 1
    assert handler.blocked_requests == 1
    assert handler.forwarded == []


def test_litellm_makes_one_call_with_no_tools_system_or_retries(monkeypatch):
    calls: list[dict] = []

    def completion(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            choices=[
                SimpleNamespace(
                    message=SimpleNamespace(content="MODEL RESPONSE"),
                    finish_reason="stop",
                )
            ],
            usage=SimpleNamespace(prompt_tokens=12, completion_tokens=7),
        )

    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = completion
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)

    result = oneshot_runner.run_litellm("EXACT PROMPT", "provider/model")

    assert calls == [
        {
            "model": "provider/model",
            "messages": [{"role": "user", "content": "EXACT PROMPT"}],
            "stream": False,
            "max_tokens": 32_768,
            "num_retries": 0,
        }
    ]
    assert result.text == "MODEL RESPONSE"
    assert (result.input_tokens, result.output_tokens) == (12, 7)
    assert result.usage_details == (
        {
            "source": "litellm_response_usage",
            "input_tokens": 12,
            "output_tokens": 7,
            "finish_reason": "stop",
        },
    )
    assert result.audit["litellm_completion_invocations"] == 1
    assert result.audit["wire_audited"] is False
    assert result.audit["litellm_retries_disabled"] is True

    reasoned_result = oneshot_runner.run_litellm("EXACT PROMPT", "provider/model", "low")
    assert calls[-1]["reasoning_effort"] == "low"
    assert reasoned_result.audit["reasoning_effort"] == "low"
    assert result.audit["system_supplied"] is False
    assert result.audit["tools_supplied"] is False
    assert result.audit["finish_reason"] == "stop"
    assert "EXACT PROMPT" not in json.dumps(result.audit)


def test_litellm_clamps_output_budget_to_pinned_model_metadata(monkeypatch):
    calls: list[dict] = []

    def completion(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            choices=[SimpleNamespace(message=SimpleNamespace(content="MODEL RESPONSE"))],
            usage=None,
        )

    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = completion
    fake_litellm.model_cost = {"provider/small-model": {"max_output_tokens": 8_192}}
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)

    result = oneshot_runner.run_litellm("EXACT PROMPT", "provider/small-model")

    assert calls[0]["max_tokens"] == 8_192
    assert result.audit["max_tokens"] == 8_192
    assert (result.input_tokens, result.output_tokens) == (None, None)


def test_main_preserves_missing_litellm_usage_as_null(monkeypatch, capsys, tmp_path):
    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = lambda **_kwargs: SimpleNamespace(
        choices=[SimpleNamespace(message=SimpleNamespace(content="MODEL RESPONSE"))]
    )
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "litellm",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "provider/model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "model_requests": 1,
        "source": "litellm_response_usage",
        "complete": False,
        "is_lower_bound": True,
    }

    output = tmp_path / "output.jsonl"
    output.write_text("".join(json.dumps(event) + "\n" for event in events))
    backend = LiteLLMOneShotBackend(model="provider/model")
    _transcript, input_tokens, output_tokens = backend.parse_output(str(output))
    usage = backend.parse_usage(str(output), input_tokens=input_tokens, output_tokens=output_tokens)

    assert usage.status == "lower_bound"
    assert usage.model_requests == 1
    assert usage.input_tokens is None
    assert usage.output_tokens is None


def test_main_preserves_explicit_litellm_zero_usage(monkeypatch, capsys, tmp_path):
    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = lambda **_kwargs: SimpleNamespace(
        choices=[SimpleNamespace(message=SimpleNamespace(content="MODEL RESPONSE"))],
        usage=SimpleNamespace(prompt_tokens=0, completion_tokens=0),
    )
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "litellm",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "provider/model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "input_tokens": 0,
        "output_tokens": 0,
        "model_requests": 1,
        "source": "litellm_response_usage",
        "complete": True,
        "is_lower_bound": False,
    }


def test_main_emits_success_terminal_result(monkeypatch, capsys, tmp_path):
    monkeypatch.setattr(
        oneshot_runner,
        "run_litellm",
        lambda _prompt, _model: oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            12,
            7,
            {
                "provider": "litellm",
                "model": "provider/model",
                "litellm_completion_invocations": 1,
                "wire_audited": False,
                "litellm_retries_disabled": True,
                "system_supplied": False,
                "tools_supplied": False,
            },
            (
                {
                    "source": "litellm_response_usage",
                    "input_tokens": 12,
                    "output_tokens": 7,
                },
            ),
        ),
    )
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "litellm",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "provider/model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    assert [event["type"] for event in events] == [
        "model_output_observed",
        "response",
        "usage",
        "request_audit",
        "result",
    ]
    assert events[-1] == {"type": "result", "status": "success", "model_requests": 1}


def test_main_emits_rich_copilot_usage_details(monkeypatch, capsys, tmp_path):
    details = (
        {
            "source": "github_copilot_sdk",
            "input_tokens": 100,
            "output_tokens": 40,
            "cache_read_input_tokens": 60,
            "cache_write_input_tokens": 10,
            "reasoning_output_tokens": 25,
            "model": "test-model-resolved",
            "duration_secs": 0.9,
            "costs": [
                {
                    "amount": 123_000_000.0,
                    "unit": "nano_aiu",
                    "source": "assistant.usage.copilot_usage.total_nano_aiu",
                }
            ],
        },
    )

    async def fake_run_copilot(*_args, **_kwargs):
        return oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            100,
            40,
            {"provider": "copilot", "inference_requests": 1},
            details,
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "model_requests": 1,
        "source": "github_copilot_sdk",
        "complete": True,
        "is_lower_bound": False,
        **details[0],
    }


def test_main_counts_retried_request_with_missing_usage_as_lower_bound(monkeypatch, capsys, tmp_path):
    details = (
        {
            "source": "github_copilot_sdk",
            "input_tokens": 100,
            "output_tokens": 40,
            "costs": [
                {
                    "amount": 123_000_000.0,
                    "unit": "nano_aiu",
                    "source": "assistant.usage.copilot_usage.total_nano_aiu",
                }
            ],
        },
    )

    async def fake_run_copilot(*_args, **_kwargs):
        return oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            100,
            40,
            {
                "provider": "copilot",
                "model_requests": 2,
                "inference_requests": 2,
            },
            details,
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_events = [event for event in events if event["type"] == "usage"]
    assert len(usage_events) == 2
    assert usage_events[0]["input_tokens"] == 100
    assert usage_events[0]["complete"] is False
    assert usage_events[0]["is_lower_bound"] is True
    assert usage_events[1] == {
        "type": "usage",
        "model_requests": 1,
        "source": "copilot_oneshot_runner",
        "complete": False,
        "is_lower_bound": True,
        "usage_unavailable": True,
    }
    assert events[-1] == {
        "type": "result",
        "status": "success",
        "model_requests": 2,
    }


def test_main_discards_usage_records_beyond_audited_requests(monkeypatch, capsys, tmp_path):
    details = tuple(
        {
            "source": "github_copilot_sdk",
            "input_tokens": 100 + attempt,
            "output_tokens": 40 + attempt,
        }
        for attempt in range(3)
    )

    async def fake_run_copilot(*_args, **_kwargs):
        return oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            303,
            123,
            {
                "provider": "copilot",
                "model_requests": 2,
                "inference_requests": 2,
            },
            details,
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_events = [event for event in events if event["type"] == "usage"]
    assert len(usage_events) == 2
    assert all(event["model_requests"] == 1 for event in usage_events)
    assert all(event["usage_unavailable"] is True for event in usage_events)
    assert all(event["usage_record_mismatch"] is True for event in usage_events)
    assert all("input_tokens" not in event and "output_tokens" not in event for event in usage_events)


def test_main_does_not_treat_missing_copilot_usage_event_as_exact_zero(monkeypatch, capsys, tmp_path):
    async def fake_run_copilot(*_args, **_kwargs):
        return oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            None,
            None,
            {"provider": "copilot", "inference_requests": 1},
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "model_requests": 1,
        "source": "copilot_oneshot_runner",
        "complete": False,
        "is_lower_bound": True,
    }


def test_provider_registry_adds_backend_without_runner_branch(monkeypatch, capsys, tmp_path):
    captured = {}

    class FakeProvider:
        audit = {
            "provider": "fake",
            "model_requests": 1,
            "audit_scope": "adapter",
            "contract_ok": True,
        }

        def invoke(self, on_timeout):
            return oneshot_runner.ProviderResult("FAKE RESPONSE", 4, 2, self.audit)

    def factory(prompt, model, workspace, deadline):
        captured.update(prompt=prompt, model=model, workspace=workspace, deadline=deadline)
        return FakeProvider()

    oneshot_runner.register_provider("fake", factory)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))
    try:
        exit_code = oneshot_runner.main(
            [
                "--provider",
                "fake",
                "--workspace",
                str(tmp_path),
                "--result-dir",
                str(tmp_path),
                "--model",
                "fake-model",
            ]
        )
    finally:
        oneshot_runner._PROVIDER_REGISTRY.pop("fake")

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert exit_code == 0
    assert captured == {
        "prompt": "EXACT PROMPT",
        "model": "fake-model",
        "workspace": str(tmp_path),
        "deadline": None,
    }
    assert [event["type"] for event in events] == [
        "model_output_observed",
        "response",
        "usage",
        "request_audit",
        "result",
    ]
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "input_tokens": 4,
        "output_tokens": 2,
        "model_requests": 1,
        "source": "fake_oneshot_runner",
        "complete": True,
        "is_lower_bound": False,
    }


def test_main_persists_response_before_provider_teardown_failure(monkeypatch, capsys, tmp_path):
    audit = {"provider": "early-response", "model_requests": 1}

    class FakeProvider:
        on_response = None

        @property
        def audit(self):
            return audit

        def set_output_callbacks(self, on_response, _on_model_output):
            self.on_response = on_response

        def invoke(self, _on_timeout):
            assert self.on_response is not None
            self.on_response("COMPLETE RESPONSE")
            raise oneshot_runner.ProviderRunError("cleanup reset", audit, retryable=False)

    oneshot_runner.register_provider("early-response", lambda *_args: FakeProvider())
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))
    try:
        exit_code = oneshot_runner.main(
            [
                "--provider",
                "early-response",
                "--workspace",
                str(tmp_path),
                "--result-dir",
                str(tmp_path),
                "--model",
                "fake-model",
            ]
        )
    finally:
        oneshot_runner._PROVIDER_REGISTRY.pop("early-response")

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert exit_code == 1
    assert [event["type"] for event in events] == [
        "model_output_observed",
        "response",
        "usage",
        "request_audit",
        "error",
        "result",
    ]
    assert events[0] == {"type": "model_output_observed", "kind": "response", "model_requests": 1}
    assert events[1] == {"type": "response", "text": "COMPLETE RESPONSE"}
    assert next(event for event in events if event["type"] == "usage")["model_requests"] == 1
    assert events[-1] == {
        "type": "result",
        "status": "error",
        "model_requests": 1,
        "retryable": False,
    }


def test_main_persists_partial_output_marker_before_provider_failure(monkeypatch, capsys, tmp_path):
    audit = {"provider": "partial-output", "model_requests": 1}

    class FakeProvider:
        on_model_output = None

        @property
        def audit(self):
            return audit

        def set_output_callbacks(self, _on_response, on_model_output):
            self.on_model_output = on_model_output

        def invoke(self, _on_timeout):
            assert self.on_model_output is not None
            self.on_model_output("assistant.message_delta")
            raise oneshot_runner.ProviderRunError("stream reset", audit, retryable=False)

    oneshot_runner.register_provider("partial-output", lambda *_args: FakeProvider())
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))
    try:
        exit_code = oneshot_runner.main(
            [
                "--provider",
                "partial-output",
                "--workspace",
                str(tmp_path),
                "--result-dir",
                str(tmp_path),
                "--model",
                "fake-model",
            ]
        )
    finally:
        oneshot_runner._PROVIDER_REGISTRY.pop("partial-output")

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert exit_code == 1
    assert events[0] == {
        "type": "model_output_observed",
        "kind": "assistant.message_delta",
        "model_requests": 1,
    }
    assert "response" not in [event["type"] for event in events]
    assert events[-1]["retryable"] is False


def test_main_ignores_response_after_terminal_timeout(monkeypatch, capsys, tmp_path):
    audit = {"provider": "late-response", "model_requests": 1}

    class FakeProvider:
        on_response = None

        @property
        def audit(self):
            return audit

        def set_output_callbacks(self, on_response, _on_model_output):
            self.on_response = on_response

        def invoke(self, on_timeout):
            error = oneshot_runner.ProviderTimeoutError("deadline", audit)
            on_timeout(error)
            assert self.on_response is not None
            self.on_response("LATE RESPONSE")
            return oneshot_runner.ProviderResult("LATE RESPONSE", None, None, audit)

    oneshot_runner.register_provider("late-response", lambda *_args: FakeProvider())
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))
    try:
        exit_code = oneshot_runner.main(
            [
                "--provider",
                "late-response",
                "--workspace",
                str(tmp_path),
                "--result-dir",
                str(tmp_path),
                "--model",
                "fake-model",
            ]
        )
    finally:
        oneshot_runner._PROVIDER_REGISTRY.pop("late-response")

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert exit_code == 1
    assert "response" not in [event["type"] for event in events]
    assert events[-1] == {"type": "result", "status": "timeout", "model_requests": 1}


def test_custom_provider_can_report_unavailable_usage(monkeypatch, capsys, tmp_path):
    class FakeProvider:
        audit = {"provider": "missing-usage", "model_requests": 1}

        def invoke(self, _on_timeout):
            return oneshot_runner.ProviderResult("FAKE RESPONSE", None, None, self.audit)

    oneshot_runner.register_provider("missing-usage", lambda *_args: FakeProvider())
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))
    try:
        exit_code = oneshot_runner.main(
            [
                "--provider",
                "missing-usage",
                "--workspace",
                str(tmp_path),
                "--result-dir",
                str(tmp_path),
                "--model",
                "fake-model",
            ]
        )
    finally:
        oneshot_runner._PROVIDER_REGISTRY.pop("missing-usage")

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert exit_code == 0
    usage_event = next(event for event in events if event["type"] == "usage")
    assert usage_event == {
        "type": "usage",
        "model_requests": 1,
        "source": "missing-usage_oneshot_runner",
        "complete": False,
        "is_lower_bound": True,
    }


def test_main_preserves_one_request_audit_when_response_parsing_fails(monkeypatch, capsys, tmp_path):
    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = lambda **_kwargs: SimpleNamespace(
        choices=[],
        usage=SimpleNamespace(prompt_tokens=123, completion_tokens=45),
    )
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "litellm",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "provider/model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 1
    assert [event["type"] for event in events] == ["usage", "request_audit", "error", "result"]
    assert events[0] == {
        "type": "usage",
        "input_tokens": 123,
        "output_tokens": 45,
        "model_requests": 1,
        "source": "litellm_response_usage",
        "complete": True,
        "is_lower_bound": False,
    }
    assert events[1]["litellm_completion_invocations"] == 1
    assert events[1]["wire_audited"] is False
    assert events[-1] == {
        "type": "result",
        "status": "error",
        "model_requests": 1,
        "retryable": False,
    }


def test_main_emits_received_copilot_usage_on_failure(monkeypatch, capsys, tmp_path):
    async def fake_run_copilot(*_args, **_kwargs):
        raise oneshot_runner.ProviderRunError(
            "invalid final response",
            {"provider": "copilot", "inference_requests": 1},
            input_tokens=55,
            output_tokens=13,
            retryable=True,
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 1
    assert events[0] == {
        "type": "usage",
        "input_tokens": 55,
        "output_tokens": 13,
        "model_requests": 1,
        "source": "copilot_oneshot_runner",
        "complete": False,
        "is_lower_bound": True,
    }
    assert events[1] == {"type": "request_audit", "provider": "copilot", "inference_requests": 1}
    assert events[-1] == {
        "type": "result",
        "status": "error",
        "model_requests": 1,
        "retryable": True,
    }


def test_main_marks_provider_deadline_as_timeout(monkeypatch, capsys, tmp_path):
    async def fake_run_copilot(*_args, **_kwargs):
        raise oneshot_runner.ProviderTimeoutError(
            "Copilot request timed out after 37s",
            {"provider": "copilot", "inference_requests": 1},
            input_tokens=55,
            output_tokens=13,
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
            "--deadline",
            str(time.time() + 37),
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 1
    assert events[-1] == {"type": "result", "status": "timeout", "model_requests": 1}
    assert events[-2] == {"type": "error", "message": "Copilot request timed out after 37s"}


def test_litellm_import_failure_records_zero_completion_invocations(monkeypatch):
    monkeypatch.setitem(sys.modules, "litellm", None)

    with pytest.raises(oneshot_runner.ProviderRunError) as exc_info:
        oneshot_runner.run_litellm("EXACT PROMPT", "provider/model")

    assert exc_info.value.audit["litellm_completion_invocations"] == 0
    assert exc_info.value.audit["wire_audited"] is False
    assert (exc_info.value.input_tokens, exc_info.value.output_tokens) == (None, None)


@pytest.mark.parametrize(
    ("error_name", "status_code", "expected"),
    [
        ("ServiceUnavailableError", None, True),
        ("AuthenticationError", None, False),
        ("ProviderError", 503, True),
        ("ProviderError", 401, False),
        ("ProviderError", 501, False),
        ("ProviderError", 505, False),
        ("ProviderError", None, False),
    ],
)
def test_litellm_provider_errors_have_explicit_retryability(
    monkeypatch,
    error_name,
    status_code,
    expected,
):
    error_type = type(error_name, (RuntimeError,), {})
    error = error_type("provider failed")
    if status_code is not None:
        error.status_code = status_code

    def completion(**_kwargs):
        raise error

    fake_litellm = types.ModuleType("litellm")
    fake_litellm.completion = completion
    monkeypatch.setitem(sys.modules, "litellm", fake_litellm)

    with pytest.raises(oneshot_runner.ProviderRunError) as exc_info:
        oneshot_runner.run_litellm("EXACT PROMPT", "provider/model")

    assert exc_info.value.retryable is expected


@pytest.mark.parametrize(("status_code", "expected"), [(503, True), (401, False)])
def test_current_exception_status_overrides_prior_success(status_code, expected):
    error = RuntimeError("current provider failure")
    error.status_code = status_code

    assert oneshot_runner._is_retryable_provider_error(error, status_code=200) is expected


@pytest.mark.parametrize("error_name", ["AuthenticationError", "BadRequestError"])
def test_permanent_exception_class_overrides_prior_transient_status(error_name):
    error_type = type(error_name, (RuntimeError,), {})

    assert oneshot_runner._is_retryable_provider_error(error_type("permanent failure"), status_code=503) is False


@pytest.mark.parametrize(
    ("message", "data", "expected"),
    [
        (
            "Request session.create failed with message: Authentication failed: "
            "Failed to validate SDK token: network fetch failed: request failed",
            None,
            True,
        ),
        (
            "Request session.create failed with message: Failed to validate SDK token (503): No server",
            None,
            True,
        ),
        (
            "Request session.create failed with message: Failed to validate SDK token (401): Unauthorized",
            None,
            False,
        ),
        ("Request session.create failed with message: provider failed", {"error": {"statusCode": 503}}, True),
        ("Request session.create failed with message: provider failed", {"statusCode": 401}, False),
    ],
)
def test_copilot_session_create_json_rpc_retryability(message, data, expected):
    class JsonRpcError(RuntimeError):
        def __init__(self):
            self.code = -32603
            self.message = message
            self.data = data
            super().__init__(message)

    assert oneshot_runner._is_retryable_provider_error(JsonRpcError()) is expected


@pytest.mark.parametrize("error_name", ["ProcessExitedError", "RuntimeError"])
def test_copilot_runtime_process_exit_is_startup_retryable(error_name):
    error_type = RuntimeError if error_name == "RuntimeError" else type(error_name, (RuntimeError,), {})
    error = error_type("CLI process exited before announcing port")

    assert oneshot_runner._is_retryable_provider_error(error) is True


@pytest.mark.parametrize(
    ("data", "expected"),
    [
        (SimpleNamespace(recoverable=False), False),
        (SimpleNamespace(error_type="invalid_model"), False),
        (
            SimpleNamespace(
                status_code=400,
                bad_request_kind="bodyless",
                error_type="bad_request",
            ),
            True,
        ),
        (SimpleNamespace(statusCode=400, badRequestKind="structured_error"), False),
        (SimpleNamespace(statusCode=503), True),
        (SimpleNamespace(statusCode=401), False),
    ],
)
def test_copilot_structured_error_retryability(data, expected):
    event = SimpleNamespace(type="session.error", data=data)

    assert oneshot_runner._copilot_event_error_retryability([event]) is expected


@pytest.mark.parametrize(
    ("bad_request_kind", "retry_allowed"),
    [("bodyless", True), ("structured_error", False)],
)
def test_copilot_http_400_retry_uses_structured_bad_request_kind(bad_request_kind, retry_allowed):
    class BadRequestHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            return httpx.Response(400 if len(self.forwarded) == 1 else 200, request=request)

    handler = BadRequestHandler("EXACT PROMPT")
    handler.bind_session("session-1")
    handler.begin_agent_turn()
    request = _request(
        "https://api.githubcopilot.com/v1/messages",
        {"model": "test-model", "max_tokens": 64_000, "messages": [], "stream": True},
    )
    ctx = SimpleNamespace(session_id="session-1")

    asyncio.run(handler.send_request(request, ctx))
    event = SimpleNamespace(
        type="model.call_failure",
        data=SimpleNamespace(
            status_code=400,
            bad_request_kind=bad_request_kind,
            error_message=f"{bad_request_kind} bad request",
        ),
    )
    retryability = oneshot_runner._copilot_event_error_retryability([event])
    handler.record_event_failure(event, retryability)

    if retry_allowed:
        asyncio.run(handler.send_request(request, ctx))
        assert len(handler.forwarded) == 2
    else:
        with pytest.raises(RuntimeError, match="permanent provider error"):
            asyncio.run(handler.send_request(request, ctx))
        assert len(handler.forwarded) == 1


def test_copilot_runner_uses_empty_mode_and_strict_session_options(monkeypatch, tmp_path):
    captured: dict[str, dict] = {}

    class MessageData:
        def __init__(self, content: str) -> None:
            self.content = content

    class UsageData:
        def __init__(self, input_tokens: int, output_tokens: int, finish_reason: str | None = None) -> None:
            self.input_tokens = input_tokens
            self.output_tokens = output_tokens
            self.finish_reason = finish_reason
            self.cache_read_tokens = 12
            self.cache_write_tokens = 3
            self.reasoning_tokens = 5
            self.model = "test-model-resolved"
            self.api_endpoint = SimpleNamespace(value="/responses")
            self.duration = timedelta(milliseconds=900)
            self.api_call_id = "response-1"
            self.provider_call_id = "github-request-1"
            self.cost = 0.0123
            self.copilot_usage = SimpleNamespace(total_nano_aiu=123_000_000)

    class FakeSession:
        session_id = "session-1"

        def __init__(self, guard, on_event) -> None:
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, prompt, **kwargs):
            captured["send"] = {"prompt": prompt, **kwargs}
            request = _request(
                "https://api.githubcopilot.com/responses",
                {
                    "model": "test-model",
                    "instructions": "",
                    "input": [
                        {
                            "role": "user",
                            "content": f"<current_datetime>now</current_datetime>\n{prompt}",
                        }
                    ],
                    "tools": [],
                    "stream": True,
                },
            )
            await self.guard.send_request(request, SimpleNamespace(session_id=self.session_id))
            self.on_event(SimpleNamespace(data=UsageData(20, 8, "stop")))
            return SimpleNamespace(data=MessageData("MODEL RESPONSE"))

    class FakeClient:
        def __init__(self, **kwargs) -> None:
            captured["client"] = kwargs
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            captured["session"] = kwargs
            return FakeSession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(
        oneshot_runner,
        "_load_copilot_sdk",
        lambda: (FakeClient, MessageData, UsageData),
    )
    monkeypatch.setattr(oneshot_runner.importlib.metadata, "version", lambda _package: "1.0.7")
    for key in oneshot_runner._COPILOT_TOKEN_KEYS:
        monkeypatch.delenv(key, raising=False)
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    result = asyncio.run(
        oneshot_runner.run_copilot(
            "EXACT PROMPT",
            "test-model",
            str(tmp_path),
            time.time() + 123.0,
            handler=handler,
            reasoning_effort="medium",
        )
    )

    client_options = captured["client"]
    assert client_options["github_token"] == "secret-token"
    assert client_options["use_logged_in_user"] is False
    assert client_options["mode"] == "empty"
    assert client_options["request_handler"] is handler
    session_options = captured["session"]
    assert session_options["available_tools"] == []
    assert session_options["system_message"] == {"mode": "replace", "content": ""}
    assert session_options["capi"] == {"enable_web_socket_responses": False}
    assert session_options["infinite_sessions"] == {"enabled": False}
    assert session_options["memory"] == {"enabled": False}
    assert session_options["reasoning_effort"] == "medium"
    assert captured["send"] == {
        "prompt": "EXACT PROMPT",
        "agent_mode": "interactive",
        "timeout": None,
    }
    assert result.text == "MODEL RESPONSE"
    assert (result.input_tokens, result.output_tokens) == (20, 8)
    assert result.audit["inference_requests"] == 1
    assert result.audit["reasoning_effort"] == "medium"
    assert result.audit["wire_audited"] is True
    assert result.audit["finish_reason"] == "stop"
    assert result.usage_details == (
        {
            "source": "github_copilot_sdk",
            "input_tokens": 20,
            "output_tokens": 8,
            "cache_read_input_tokens": 12,
            "cache_write_input_tokens": 3,
            "reasoning_output_tokens": 5,
            "model": "test-model-resolved",
            "endpoint": "/responses",
            "duration_secs": 0.9,
            "finish_reason": "stop",
            "request_id": "response-1",
            "provider_request_id": "github-request-1",
            "runtime_version": "1.0.7",
            "costs": [
                {
                    "amount": 0.0123,
                    "unit": "model_multiplier",
                    "source": "assistant.usage.cost",
                },
                {
                    "amount": 123_000_000.0,
                    "unit": "nano_aiu",
                    "source": "assistant.usage.copilot_usage.total_nano_aiu",
                },
            ],
        },
    )
    assert json.loads(handler.forwarded[0].content)["input"][0]["content"][0]["text"] == "EXACT PROMPT"


@pytest.mark.parametrize("failure_mode", ["http_503", "connect_error"])
def test_copilot_native_retry_after_reasoning_completes_one_logical_turn(monkeypatch, tmp_path, failure_mode):
    send_calls = []

    class MessageData:
        def __init__(self, content):
            self.content = content
            self.tool_requests = None

    class UsageData:
        pass

    class TransientHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            if len(self.forwarded) == 1:
                if failure_mode == "connect_error":
                    raise httpx.ConnectError("connection reset", request=request)
                return httpx.Response(503, request=request)
            return httpx.Response(200, request=request)

    class RetrySession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event
            self.send_calls = 0

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            self.send_calls += 1
            send_calls.append(True)
            request = _request(
                "https://api.githubcopilot.com/responses",
                {"model": "test-model", "input": [], "stream": True},
            )
            context = {
                "session_id": self.session_id,
                "agent_id": "agent-1",
                "parent_agent_id": None,
                "interaction_type": "user",
            }
            if failure_mode == "connect_error":
                with pytest.raises(httpx.ConnectError):
                    await self.guard.send_request(
                        request,
                        SimpleNamespace(**context, request_id="request-1"),
                    )
            else:
                await self.guard.send_request(
                    request,
                    SimpleNamespace(**context, request_id="request-1"),
                )
            self.on_event(
                SimpleNamespace(
                    type="assistant.reasoning_delta",
                    data=SimpleNamespace(delta_content="PARTIAL REASONING"),
                )
            )
            await self.guard.send_request(
                request,
                SimpleNamespace(**context, request_id="request-2"),
            )
            return SimpleNamespace(data=MessageData("COMPLETE RESPONSE"))

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]
            self.session = None

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            self.session = RetrySession(self.guard, kwargs["on_event"])
            return self.session

    handler = TransientHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")
    responses = []
    observed_output = []

    result = asyncio.run(
        oneshot_runner.run_copilot(
            "EXACT PROMPT",
            "test-model",
            str(tmp_path),
            None,
            handler=handler,
            on_response=responses.append,
            on_model_output=observed_output.append,
        )
    )

    assert result.text == "COMPLETE RESPONSE"
    assert send_calls == [True]
    assert responses == ["COMPLETE RESPONSE"]
    assert observed_output == ["assistant.reasoning_delta"]
    assert len(handler.forwarded) == 2
    assert handler.forwarded[0].content == handler.forwarded[1].content
    assert result.audit["logical_agent_turns"] == 1
    assert result.audit["completed_responses"] == 1
    assert result.audit["inference_requests"] == 2
    assert result.audit["inference_attempts"] == 2
    assert result.audit["blocked_requests"] == 0
    assert result.audit["contract_ok"] is True


def test_copilot_messages_stream_retries_after_reasoning_before_one_response(monkeypatch, tmp_path):
    send_calls = []
    stream_closed = []

    class MessageData:
        def __init__(self, content):
            self.content = content
            self.tool_requests = None

    class UsageData:
        pass

    class FailingStream(httpx.AsyncByteStream):
        def __init__(self, emit_reasoning, request):
            self.emit_reasoning = emit_reasoning
            self.request = request

        async def __aiter__(self):
            self.emit_reasoning()
            raise httpx.ReadError("stream reset after reasoning", request=self.request)
            yield b""

        async def aclose(self):
            stream_closed.append(True)

    class SuccessfulStream(httpx.AsyncByteStream):
        async def __aiter__(self):
            yield b"{}"

        async def aclose(self):
            return None

    async def fake_base_forward_http(self, request, _exchange, ctx):
        response = await self.send_request(request, ctx)
        try:
            async for _chunk in response.aiter_raw():
                pass
        finally:
            await response.aclose()

    class StreamRetryHandler(oneshot_runner.StrictCopilotRequestHandler):
        def __init__(self, prompt):
            super().__init__(prompt)
            self.forwarded = []
            self.emit_reasoning = None

        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            if len(self.forwarded) == 1:
                assert self.emit_reasoning is not None
                return httpx.Response(
                    200,
                    request=request,
                    stream=FailingStream(self.emit_reasoning, request),
                )
            return httpx.Response(200, request=request, stream=SuccessfulStream())

    class RetrySession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event
            self.send_calls = 0
            self.guard.emit_reasoning = lambda: self.on_event(
                SimpleNamespace(
                    type="assistant.reasoning_delta",
                    data=SimpleNamespace(delta_content="PARTIAL REASONING"),
                )
            )

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            self.send_calls += 1
            send_calls.append(True)
            request = _request(
                "https://api.githubcopilot.com/v1/messages",
                {
                    "model": "claude-opus-4.8",
                    "max_tokens": 64_000,
                    "messages": [],
                    "stream": True,
                },
            )
            context = {
                "session_id": self.session_id,
                "agent_id": "agent-1",
                "parent_agent_id": None,
                "interaction_type": "user",
            }
            with pytest.raises(httpx.ReadError, match="stream reset after reasoning"):
                await self.guard._forward_http(
                    request,
                    object(),
                    SimpleNamespace(**context, request_id="request-1"),
                )
            await self.guard._forward_http(
                request,
                object(),
                SimpleNamespace(**context, request_id="request-2"),
            )
            return SimpleNamespace(data=MessageData("COMPLETE RESPONSE"))

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return RetrySession(self.guard, kwargs["on_event"])

    monkeypatch.setattr(
        oneshot_runner._CopilotRequestHandler,
        "_forward_http",
        fake_base_forward_http,
        raising=False,
    )
    handler = StreamRetryHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")
    responses = []
    observed_output = []

    result = asyncio.run(
        oneshot_runner.run_copilot(
            "EXACT PROMPT",
            "claude-opus-4.8",
            str(tmp_path),
            None,
            handler=handler,
            on_response=responses.append,
            on_model_output=observed_output.append,
        )
    )

    assert result.text == "COMPLETE RESPONSE"
    assert send_calls == [True]
    assert responses == ["COMPLETE RESPONSE"]
    assert observed_output == ["assistant.reasoning_delta"]
    assert stream_closed == [True]
    assert len(handler.forwarded) == 2
    assert [request.url.path for request in handler.forwarded] == ["/v1/messages", "/v1/messages"]
    assert handler.forwarded[0].content == handler.forwarded[1].content
    assert json.loads(handler.forwarded[0].content)["messages"] == [{"role": "user", "content": "EXACT PROMPT"}]
    assert result.audit["logical_agent_turns"] == 1
    assert result.audit["completed_responses"] == 1
    assert result.audit["inference_requests"] == 2
    assert result.audit["blocked_requests"] == 0
    details = result.audit["inference_request_details"]
    assert details[0]["stream_completed"] is False
    assert details[0]["retryable"] is True
    assert details[0]["error_type"] == "ReadError"
    assert details[1]["stream_completed"] is True
    assert result.audit["contract_ok"] is True


def test_copilot_permanent_failure_is_preserved_when_runtime_attempts_retry(monkeypatch, tmp_path):
    class MessageData:
        pass

    class UsageData:
        pass

    class RetrySession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            request = _request(
                "https://api.githubcopilot.com/responses",
                {"model": "invalid-model", "input": [], "stream": True},
            )
            ctx = SimpleNamespace(session_id=self.session_id)
            await self.guard.send_request(request, ctx)
            self.on_event(
                SimpleNamespace(
                    type="session.error",
                    data=SimpleNamespace(
                        status_code=401,
                        message="invalid model credentials",
                    ),
                )
            )
            try:
                return await self.guard.send_request(request, ctx)
            except RuntimeError as exc:
                raise RuntimeError(f"Session error: Execution failed; Last error: {exc}") from exc

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return RetrySession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError, match="invalid model credentials") as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "invalid-model",
                str(tmp_path),
                None,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is False
    assert len(handler.forwarded) == 1
    assert exc_info.value.audit["inference_requests"] == 1
    assert exc_info.value.audit["inference_attempts"] == 2
    assert exc_info.value.audit["blocked_requests"] == 1
    assert exc_info.value.audit["inference_request_details"][0]["status_code"] == 401


def test_copilot_changed_native_retry_is_not_outer_retryable(monkeypatch, tmp_path):
    class MessageData:
        pass

    class UsageData:
        pass

    class TransientHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            return httpx.Response(503, request=request)

    class ChangedRetrySession:
        session_id = "session-1"

        def __init__(self, guard):
            self.guard = guard

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            ctx = SimpleNamespace(session_id=self.session_id)
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                ctx,
            )
            return await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "different-model", "input": [], "stream": True},
                ),
                ctx,
            )

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **_kwargs):
            return ChangedRetrySession(self.guard)

    handler = TransientHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError, match="changed request") as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is False
    assert exc_info.value.audit["contract_ok"] is False
    assert exc_info.value.audit["inference_requests"] == 1
    assert exc_info.value.audit["inference_attempts"] == 2
    assert exc_info.value.audit["blocked_requests"] == 1


@pytest.mark.parametrize(
    ("event_type", "event_data"),
    [
        ("assistant.message_delta", SimpleNamespace(delta_content="PARTIAL RESPONSE")),
        ("assistant.message_delta", SimpleNamespace(delta_content="\n")),
        ("assistant.reasoning_delta", SimpleNamespace(delta_content="PARTIAL REASONING")),
        ("assistant.reasoning_delta", SimpleNamespace(delta_content=" ")),
        ("assistant.reasoning", SimpleNamespace(content="COMPLETE REASONING")),
        ("assistant.tool_call_delta", SimpleNamespace(input_delta="{}")),
    ],
)
def test_copilot_streamed_model_output_blocks_outer_retry(monkeypatch, tmp_path, event_type, event_data):
    class MessageData:
        pass

    class UsageData:
        pass

    class PartialOutputSession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                SimpleNamespace(session_id=self.session_id),
            )
            self.on_event(SimpleNamespace(type=event_type, data=event_data))
            raise ConnectionError("stream reset after partial output")

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return PartialOutputSession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError, match="partial output") as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is False
    assert exc_info.value.audit["model_requests"] == 1
    assert (exc_info.value.input_tokens, exc_info.value.output_tokens) == (None, None)


@pytest.mark.parametrize("output_tokens", [None, 0])
def test_copilot_reasoning_usage_blocks_outer_retry(monkeypatch, tmp_path, output_tokens):
    class MessageData:
        pass

    class UsageData:
        def __init__(self):
            self.input_tokens = 100
            self.output_tokens = output_tokens
            self.reasoning_tokens = 9

    class ReasoningUsageSession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                SimpleNamespace(session_id=self.session_id),
            )
            self.on_event(SimpleNamespace(type="assistant.usage", data=UsageData()))
            raise ConnectionError("stream reset after reasoning usage")

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return ReasoningUsageSession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    observed_output = []
    with pytest.raises(oneshot_runner.ProviderRunError, match="reasoning usage") as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
                on_model_output=observed_output.append,
            )
        )

    assert observed_output == ["assistant.usage"]
    assert exc_info.value.retryable is False
    assert (exc_info.value.input_tokens, exc_info.value.output_tokens) == (100, output_tokens)
    assert exc_info.value.usage_details[0]["reasoning_output_tokens"] == 9


@pytest.mark.parametrize(
    ("event_type", "status_code", "message", "blocked_retry", "expected"),
    [
        ("session.error", 503, "provider unavailable", False, True),
        ("model.call_failure", 503, "provider unavailable", True, True),
        ("session.error", 401, "unauthorized", False, False),
        ("session.error", None, "Execution failed: Error: All connection attempts failed", True, True),
        ("session.error", None, "Execution failed; Last error: 503 provider unavailable", True, True),
        ("model.call_failure", None, "Last error: 401 unauthorized", False, False),
    ],
)
def test_copilot_structured_failure_event_controls_outer_retry(
    monkeypatch,
    tmp_path,
    event_type,
    status_code,
    message,
    blocked_retry,
    expected,
):
    class MessageData:
        pass

    class UsageData:
        pass

    class FailureEventSession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            request = _request(
                "https://api.githubcopilot.com/responses",
                {"model": "test-model", "input": [], "stream": True},
            )
            ctx = SimpleNamespace(session_id=self.session_id)
            await self.guard.send_request(request, ctx)
            self.on_event(
                SimpleNamespace(
                    type=event_type,
                    data=SimpleNamespace(
                        status_code=status_code,
                        message=message,
                        error_message=message,
                    ),
                )
            )
            if blocked_retry:
                return await self.guard.send_request(request, ctx)
            raise RuntimeError("SDK discarded structured provider error")

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return FailureEventSession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError) as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is expected
    assert exc_info.value.audit["inference_requests"] == 1 + int(blocked_retry)
    assert exc_info.value.audit["blocked_requests"] == 0


@pytest.mark.parametrize("permanent_channel", ["inference", "aux"])
def test_copilot_permanent_status_overrides_cross_channel_transient(monkeypatch, tmp_path, permanent_channel):
    class MessageData:
        pass

    class UsageData:
        pass

    class MixedStatusHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            is_aux = str(request.url).endswith("/models")
            status = (
                401
                if (is_aux and permanent_channel == "aux") or (not is_aux and permanent_channel == "inference")
                else 503
            )
            return httpx.Response(status, request=request)

    class MixedStatusSession:
        session_id = "session-1"

        def __init__(self, guard):
            self.guard = guard

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            ctx = SimpleNamespace(session_id=self.session_id)
            inference = _request(
                "https://api.githubcopilot.com/responses",
                {"model": "test-model", "input": [], "stream": True},
            )
            await self.guard.send_request(inference, ctx)
            auxiliary = await self.guard.send_request(_request("https://api.githubcopilot.com/models"), ctx)
            if permanent_channel == "aux":
                auxiliary.raise_for_status()
            return await self.guard.send_request(inference, ctx)

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **_kwargs):
            return MixedStatusSession(self.guard)

    handler = MixedStatusHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError) as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is False
    assert exc_info.value.audit["inference_requests"] == 1
    assert exc_info.value.audit["blocked_requests"] == (1 if permanent_channel == "inference" else 0)


def test_copilot_guard_deadline_race_is_timeout_not_retryable(monkeypatch, tmp_path):
    clock = [0.0]

    class MessageData:
        pass

    class UsageData:
        pass

    class TransientHandler(_RecordingHandler):
        async def _forward(self, request, _ctx):
            self.forwarded.append(request)
            return httpx.Response(503, request=request)

    class DeadlineSession:
        session_id = "session-1"

        def __init__(self, guard):
            self.guard = guard

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            request = _request(
                "https://api.githubcopilot.com/responses",
                {"model": "test-model", "input": [], "stream": True},
            )
            await self.guard.send_request(request, SimpleNamespace(session_id=self.session_id))
            clock[0] = 11.0
            return await self.guard.send_request(request, SimpleNamespace(session_id=self.session_id))

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **_kwargs):
            return DeadlineSession(self.guard)

    handler = TransientHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setattr(oneshot_runner.time, "time", lambda: clock[0])
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderTimeoutError) as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                10.0,
                handler=handler,
            )
        )

    assert exc_info.value.retryable is False
    assert exc_info.value.audit["deadline_closed"] is True
    assert exc_info.value.audit["contract_ok"] is True
    assert exc_info.value.audit["inference_requests"] == 1
    assert exc_info.value.audit["inference_attempts"] == 1
    assert exc_info.value.audit["blocked_requests"] == 0
    assert exc_info.value.audit["deadline_blocked_requests"] == 1


@pytest.mark.parametrize("failure_phase", ["send", "teardown"])
def test_copilot_emits_complete_response_before_late_failure(monkeypatch, tmp_path, failure_phase):
    class MessageData:
        def __init__(self, content):
            self.content = content

    class UsageData:
        pass

    class FailingSession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            if failure_phase == "teardown":
                raise ConnectionError("teardown reset")
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                SimpleNamespace(session_id=self.session_id),
            )
            event = SimpleNamespace(data=MessageData("COMPLETE RESPONSE"))
            if failure_phase == "send":
                self.on_event(event)
                raise ConnectionError("send reset")
            return event

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return FailingSession(self.guard, kwargs["on_event"])

    emitted_responses = []
    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError, match="reset") as exc_info:
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                None,
                handler=handler,
                on_response=emitted_responses.append,
            )
        )

    assert emitted_responses == ["COMPLETE RESPONSE"]
    assert exc_info.value.retryable is False
    assert exc_info.value.audit["model_requests"] == 1
    assert (exc_info.value.input_tokens, exc_info.value.output_tokens) == (None, None)


@pytest.mark.parametrize(
    ("failure_mode", "error_message"),
    [
        ("final", "Copilot returned no final assistant message"),
        ("guard", "strict one-shot: logical agent turn did not produce one clean response"),
        ("session", "session failed after usage"),
        ("transport_timeout", "transport timed out"),
        ("timeout", "Copilot request reached benchmark deadline"),
    ],
)
def test_copilot_failure_preserves_received_usage(monkeypatch, tmp_path, failure_mode, error_message):
    class MessageData:
        def __init__(self, content: str) -> None:
            self.content = content

    class UsageData:
        def __init__(self, input_tokens: int, output_tokens: int, finish_reason: str | None = None) -> None:
            self.input_tokens = input_tokens
            self.output_tokens = output_tokens
            self.finish_reason = finish_reason
            self.cache_read_tokens = 12
            self.cache_write_tokens = 3
            self.reasoning_tokens = 5
            self.model = "test-model"
            self.api_endpoint = SimpleNamespace(value="/responses")
            self.duration = timedelta(milliseconds=900)
            self.cost = 0.0123
            self.copilot_usage = SimpleNamespace(total_nano_aiu=123_000_000)

    class FakeSession:
        session_id = "session-1"

        def __init__(self, guard, on_event) -> None:
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def send_and_wait(self, _prompt, **_kwargs):
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                SimpleNamespace(session_id=self.session_id),
            )
            self.on_event(SimpleNamespace(data=UsageData(20, 8, "length")))
            if failure_mode == "session":
                raise RuntimeError("session failed after usage")
            if failure_mode == "transport_timeout":
                raise TimeoutError("transport timed out")
            if failure_mode == "timeout":
                await asyncio.sleep(60)
            if failure_mode == "guard":
                self.guard.blocked_requests += 1
                return SimpleNamespace(data=MessageData("MODEL RESPONSE"))
            return SimpleNamespace(data=object())

    class FakeClient:
        def __init__(self, **kwargs) -> None:
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return FakeSession(self.guard, kwargs["on_event"])

    handler = _RecordingHandler("EXACT PROMPT")
    monkeypatch.setattr(
        oneshot_runner,
        "_load_copilot_sdk",
        lambda: (FakeClient, MessageData, UsageData),
    )
    for key in oneshot_runner._COPILOT_TOKEN_KEYS:
        monkeypatch.delenv(key, raising=False)
    monkeypatch.setenv("GH_TOKEN", "secret-token")

    with pytest.raises(oneshot_runner.ProviderRunError, match=error_message) as exc_info:
        deadline = time.time() + 0.1 if failure_mode == "timeout" else None
        asyncio.run(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                deadline,
                handler=handler,
            )
        )

    assert (exc_info.value.input_tokens, exc_info.value.output_tokens) == (20, 8)
    assert exc_info.value.audit["inference_requests"] == 1
    assert exc_info.value.audit["finish_reason"] == "length"
    assert exc_info.value.usage_details[0]["cache_read_input_tokens"] == 12
    assert exc_info.value.usage_details[0]["cache_write_input_tokens"] == 3
    assert exc_info.value.usage_details[0]["reasoning_output_tokens"] == 5
    assert exc_info.value.usage_details[0]["duration_secs"] == 0.9
    assert [cost["unit"] for cost in exc_info.value.usage_details[0]["costs"]] == [
        "model_multiplier",
        "nano_aiu",
    ]
    if failure_mode == "timeout":
        assert isinstance(exc_info.value, oneshot_runner.ProviderTimeoutError)
    if failure_mode == "transport_timeout":
        assert not isinstance(exc_info.value, oneshot_runner.ProviderTimeoutError)
    assert exc_info.value.retryable is False


def test_copilot_timeout_is_reported_before_slow_sdk_teardown(monkeypatch, tmp_path):
    class MessageData:
        pass

    class UsageData:
        def __init__(self, input_tokens, output_tokens):
            self.input_tokens = input_tokens
            self.output_tokens = output_tokens
            self.finish_reason = "length"

    class SlowExitSession:
        session_id = "session-1"

        def __init__(self, guard, on_event):
            self.guard = guard
            self.on_event = on_event

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            await asyncio.sleep(60)

        async def send_and_wait(self, _prompt, **_kwargs):
            await self.guard.send_request(
                _request(
                    "https://api.githubcopilot.com/responses",
                    {"model": "test-model", "input": [], "stream": True},
                ),
                SimpleNamespace(session_id=self.session_id),
            )
            self.on_event(SimpleNamespace(data=UsageData(21, 8)))
            await asyncio.sleep(60)

    class FakeClient:
        def __init__(self, **kwargs):
            self.guard = kwargs["request_handler"]

        async def __aenter__(self):
            return self

        async def __aexit__(self, *_args):
            return None

        async def create_session(self, **kwargs):
            return SlowExitSession(self.guard, kwargs["on_event"])

    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (FakeClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")
    captured = []

    async def scenario():
        emitted = asyncio.Event()

        def on_timeout(exc):
            captured.append(exc)
            emitted.set()

        task = asyncio.create_task(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                time.time() + 0.02,
                handler=_RecordingHandler("EXACT PROMPT"),
                on_timeout=on_timeout,
            )
        )
        await asyncio.wait_for(emitted.wait(), timeout=0.5)
        assert not task.done(), "timeout must be durable before slow SDK teardown completes"
        task.cancel()
        with pytest.raises(oneshot_runner.ProviderTimeoutError):
            await task

    asyncio.run(scenario())

    assert len(captured) == 1
    assert isinstance(captured[0], oneshot_runner.ProviderTimeoutError)
    assert (captured[0].input_tokens, captured[0].output_tokens) == (21, 8)
    assert captured[0].audit["model_requests"] == 1


def test_copilot_deadline_watchdog_covers_sdk_startup(monkeypatch, tmp_path):
    class MessageData:
        pass

    class UsageData:
        pass

    class SlowStartClient:
        def __init__(self, **_kwargs):
            pass

        async def __aenter__(self):
            await asyncio.sleep(60)

        async def __aexit__(self, *_args):
            return None

    monkeypatch.setattr(oneshot_runner, "_load_copilot_sdk", lambda: (SlowStartClient, MessageData, UsageData))
    monkeypatch.setenv("GH_TOKEN", "secret-token")
    captured = []

    async def scenario():
        task = asyncio.create_task(
            oneshot_runner.run_copilot(
                "EXACT PROMPT",
                "test-model",
                str(tmp_path),
                time.time() + 0.02,
                on_timeout=captured.append,
            )
        )
        with pytest.raises(oneshot_runner.ProviderTimeoutError):
            await asyncio.wait_for(task, timeout=0.5)

    asyncio.run(scenario())

    assert len(captured) == 1
    assert captured[0].audit["deadline_closed"] is True
    assert captured[0].audit["model_requests"] == 0


@pytest.mark.parametrize("deadline_arg", ["0", "-5"])
def test_main_maps_nonpositive_copilot_deadline_to_none(monkeypatch, capsys, tmp_path, deadline_arg):
    captured_deadlines: list[float | None] = []

    async def fake_run_copilot(
        _prompt,
        _model,
        _workspace,
        deadline,
        handler=None,
        on_timeout=None,
        on_response=None,
        on_model_output=None,
    ):
        captured_deadlines.append(deadline)
        return oneshot_runner.ProviderResult(
            "MODEL RESPONSE",
            12,
            7,
            {"provider": "copilot", "inference_requests": 1},
        )

    monkeypatch.setattr(oneshot_runner, "run_copilot", fake_run_copilot)
    monkeypatch.setattr(sys, "stdin", io.StringIO("EXACT PROMPT"))

    exit_code = oneshot_runner.main(
        [
            "--provider",
            "copilot",
            "--workspace",
            str(tmp_path),
            "--result-dir",
            str(tmp_path),
            "--model",
            "test-model",
            "--deadline",
            deadline_arg,
        ]
    )
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]

    assert exit_code == 0
    assert captured_deadlines == [None]
    assert events[-1] == {"type": "result", "status": "success", "model_requests": 1}
