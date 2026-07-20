"""In-container LiteLLM agent usage emission."""

from __future__ import annotations

import json
from types import SimpleNamespace

import pytest

litellm_agent = pytest.importorskip(
    "evaluator.backends.litellm_agent",
    reason="litellm is only installed inside the agent container",
)


class _FakeResponse:
    def __init__(self, *, usage=None, model="claude-sonnet-4-6", response_id="chatcmpl-1", hidden=None, finish="stop"):
        self.usage = usage
        self.model = model
        self.id = response_id
        self.choices = [SimpleNamespace(finish_reason=finish)]
        if hidden is not None:
            self._hidden_params = hidden


def _usage(**kwargs):
    return SimpleNamespace(**kwargs)


def _emit(capsys, response, iteration=1, elapsed=1.25):
    litellm_agent._emit_request_usage(response, iteration, elapsed)
    out = capsys.readouterr().out.strip()
    return json.loads(out) if out else None


def test_hidden_response_cost_is_preferred(capsys):
    response = _FakeResponse(
        usage=_usage(prompt_tokens=100, completion_tokens=10),
        hidden={"response_cost": 0.0042},
    )

    event = _emit(capsys, response)

    assert event["costs"] == [{"amount": 0.0042, "unit": "usd", "source": "litellm.response_cost"}]
    assert event["input_tokens"] == 100
    assert event["output_tokens"] == 10


def test_completion_cost_is_the_fallback(capsys, monkeypatch):
    monkeypatch.setattr(litellm_agent.litellm, "completion_cost", lambda **_: 0.5, raising=False)
    response = _FakeResponse(usage=_usage(prompt_tokens=10, completion_tokens=5))

    event = _emit(capsys, response)

    assert event["costs"] == [{"amount": 0.5, "unit": "usd", "source": "litellm.response_cost"}]


def test_cost_failure_omits_cost_rather_than_reporting_zero(capsys, monkeypatch):
    def _boom(**_):
        raise RuntimeError("no pricing for model")

    monkeypatch.setattr(litellm_agent.litellm, "completion_cost", _boom, raising=False)
    response = _FakeResponse(usage=_usage(prompt_tokens=10, completion_tokens=5))

    event = _emit(capsys, response)

    assert "costs" not in event


def test_cache_and_reasoning_details_are_emitted(capsys):
    response = _FakeResponse(
        usage=_usage(
            prompt_tokens=100,
            completion_tokens=40,
            prompt_tokens_details=SimpleNamespace(cached_tokens=30),
            completion_tokens_details=SimpleNamespace(reasoning_tokens=15),
        ),
        hidden={"response_cost": 0.001},
    )

    event = _emit(capsys, response)

    assert event["cache_read_input_tokens"] == 30
    assert event["reasoning_output_tokens"] == 15


def test_absent_token_fields_are_omitted_not_zeroed(capsys):
    response = _FakeResponse(usage=_usage(prompt_tokens=None, completion_tokens=7), hidden={"response_cost": 0.0})

    event = _emit(capsys, response)

    assert "input_tokens" not in event
    assert event["output_tokens"] == 7
    # An explicit zero cost is still an exact value.
    assert event["costs"] == [{"amount": 0.0, "unit": "usd", "source": "litellm.response_cost"}]


def test_response_without_usage_emits_nothing(capsys):
    assert _emit(capsys, _FakeResponse(usage=None)) is None


def test_metadata_is_carried_through(capsys):
    response = _FakeResponse(
        usage=_usage(prompt_tokens=1, completion_tokens=1),
        model="gpt-5.6",
        response_id="chatcmpl-xyz",
        finish="length",
        hidden={"response_cost": 0.01},
    )

    event = _emit(capsys, response, iteration=3, elapsed=2.5)

    assert event["model"] == "gpt-5.6"
    assert event["request_id"] == "chatcmpl-xyz"
    assert event["finish_reason"] == "length"
    assert event["iteration"] == 3
    assert event["duration_secs"] == 2.5
