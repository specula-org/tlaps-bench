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
    def __init__(self, prompt: str) -> None:
        super().__init__(prompt)
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
    assert handler.audit()["blocked_requests"] == 1
    assert handler.forwarded == []


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


def test_copilot_handler_forwards_only_rewritten_first_inference():
    handler = _RecordingHandler("EXACT PROMPT")
    handler.bind_session("session-1")
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
        "retries_enabled": False,
        "audit_scope": "wire",
        "contract_ok": True,
        "wire_audited": True,
        "inference_requests": 1,
        "inference_attempts": 1,
        "blocked_requests": 0,
        "unknown_requests": 0,
        "system_removed": True,
        "tools_removed": True,
        "deadline_closed": False,
        "endpoint": "/responses",
        "request_sha256": handler.request_sha256,
    }
    assert "secret" not in json.dumps(handler.audit())
    assert "EXACT PROMPT" not in json.dumps(handler.audit())

    with pytest.raises(RuntimeError, match="blocked inference request after the first"):
        asyncio.run(handler.send_request(original, ctx))
    assert len(handler.forwarded) == 1
    assert handler.inference_attempts == 2
    assert handler.blocked_requests == 1


def test_copilot_handler_audits_and_blocks_wrong_session_before_forwarding():
    handler = _RecordingHandler("prompt")
    handler.bind_session("expected-session")

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
    assert events[1] == {
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
    assert events[1] == {
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
    assert [event["type"] for event in events] == ["response", "usage", "request_audit", "result"]
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
    assert events[1] == {
        "type": "usage",
        "model_requests": 1,
        "source": "github_copilot_sdk",
        "complete": True,
        "is_lower_bound": False,
        **details[0],
    }


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
    assert events[1] == {
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
    assert [event["type"] for event in events] == ["response", "usage", "request_audit", "result"]
    assert events[1] == {
        "type": "usage",
        "input_tokens": 4,
        "output_tokens": 2,
        "model_requests": 1,
        "source": "fake_oneshot_runner",
        "complete": True,
        "is_lower_bound": False,
    }


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
    assert events[1] == {
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
    assert events[-1] == {"type": "result", "status": "error", "model_requests": 1}


def test_main_emits_received_copilot_usage_on_failure(monkeypatch, capsys, tmp_path):
    async def fake_run_copilot(*_args, **_kwargs):
        raise oneshot_runner.ProviderRunError(
            "invalid final response",
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
    assert events[-1] == {"type": "result", "status": "error", "model_requests": 1}


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
    assert captured["send"] == {
        "prompt": "EXACT PROMPT",
        "agent_mode": "interactive",
        "timeout": None,
    }
    assert result.text == "MODEL RESPONSE"
    assert (result.input_tokens, result.output_tokens) == (20, 8)
    assert result.audit["inference_requests"] == 1
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


@pytest.mark.parametrize(
    ("failure_mode", "error_message"),
    [
        ("final", "Copilot returned no final assistant message"),
        ("guard", "strict one-shot: expected exactly one inference attempt and one forwarded request"),
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

    async def fake_run_copilot(_prompt, _model, _workspace, deadline, handler=None, on_timeout=None):
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
