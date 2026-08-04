"""Exercise the real LiteLLM library's cost reporting against a local endpoint.

The unit tests use hand-built response objects, which cannot catch a change in
LiteLLM's own pricing API. This drives ``litellm.completion`` for real against a
local OpenAI-compatible server, so the cost path is validated end to end without
network access, credentials, or spend.
"""

from __future__ import annotations

import json
import sys
import threading
from contextlib import contextmanager, redirect_stdout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from io import StringIO

import pytest

litellm = pytest.importorskip("litellm", reason="litellm is only installed for the LiteLLM backends")

from evaluator.backends import litellm_agent  # noqa: E402
from evaluator.backends.litellm import LiteLLMBackend  # noqa: E402
from evaluator.backends.oneshot_runner import run_litellm  # noqa: E402


@contextmanager
def _openai_server(
    usage: dict,
    model: str = "gpt-4o",
    response_id: str = "chatcmpl-local",
    *,
    transient_failures: int = 0,
    request_state: dict[str, int] | None = None,
):
    state = request_state if request_state is not None else {}
    state["posts"] = 0

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, _format, *_args):
            return

        def do_POST(self):
            state["posts"] += 1
            length = int(self.headers.get("Content-Length", "0"))
            self.rfile.read(length)
            if state["posts"] <= transient_failures:
                payload = json.dumps({"error": {"message": "transient", "type": "server_error"}}).encode()
                self.send_response(500)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            payload = json.dumps(
                {
                    "id": response_id,
                    "object": "chat.completion",
                    "created": 1_784_443_000,
                    "model": model,
                    "choices": [
                        {
                            "index": 0,
                            "message": {"role": "assistant", "content": "Done."},
                            "finish_reason": "stop",
                        }
                    ],
                    "usage": usage,
                }
            ).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{server.server_port}"
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)


def _emit(response, iteration: int = 1, elapsed: float = 3.25) -> dict:
    buffer = StringIO()
    with redirect_stdout(buffer):
        litellm_agent._emit_request_usage(response, iteration, elapsed)
    printed = buffer.getvalue().strip()
    return json.loads(printed) if printed else {}


def test_real_litellm_response_reports_usd_cost_through_the_backend(tmp_path):
    usage = {
        "prompt_tokens": 1200,
        "completion_tokens": 340,
        "total_tokens": 1540,
        "prompt_tokens_details": {"cached_tokens": 800},
        "completion_tokens_details": {"reasoning_tokens": 120},
    }
    with _openai_server(usage) as base_url:
        response = litellm.completion(
            model="gpt-4o",
            messages=[{"role": "user", "content": "hi"}],
            api_base=base_url,
            api_key="test-key",
        )

    # LiteLLM populates its own cost; we must read it rather than recompute it.
    hidden = getattr(response, "_hidden_params", {})
    reported_cost = hidden.get("response_cost")
    assert isinstance(reported_cost, float) and reported_cost > 0

    event = _emit(response)
    assert event["input_tokens"] == 1200
    assert event["output_tokens"] == 340
    assert event["cache_read_input_tokens"] == 800
    assert event["reasoning_output_tokens"] == 120
    assert event["costs"] == [{"amount": reported_cost, "unit": "usd", "source": "litellm.response_cost"}]

    # Replay the agent's real stdout stream through the backend parser.
    output = tmp_path / "output.jsonl"
    output.write_text(
        json.dumps(event)
        + "\n"
        + json.dumps({"type": "response", "text": "Done.", "iteration": 1})
        + "\n"
        + json.dumps({"type": "usage", "input_tokens": 1200, "output_tokens": 340, "model_requests": 1})
        + "\n"
    )

    backend = LiteLLMBackend(model="gpt-4o")
    _, legacy_in, legacy_out = backend.parse_output(str(output))
    usage_summary = backend.parse_usage(str(output), input_tokens=legacy_in, output_tokens=legacy_out)

    assert usage_summary.status == "complete"
    assert usage_summary.input_tokens == 1200
    assert usage_summary.cache_read_input_tokens == 800
    assert usage_summary.reasoning_output_tokens == 120
    assert [cost.to_dict() for cost in usage_summary.costs] == [
        {"amount": reported_cost, "unit": "usd", "source": "litellm.response_cost"}
    ]
    # The structured record must not change the legacy top-level numbers.
    assert (usage_summary.legacy_input_tokens, usage_summary.legacy_output_tokens) == (legacy_in, legacy_out)


def test_reported_cost_accounts_for_cached_token_discounts():
    """LiteLLM's price is not a naive tokens x rate product."""

    plain = {"prompt_tokens": 1200, "completion_tokens": 340, "total_tokens": 1540}
    cached = {
        "prompt_tokens": 1200,
        "completion_tokens": 340,
        "total_tokens": 1540,
        "prompt_tokens_details": {"cached_tokens": 800},
    }
    costs = []
    for usage in (plain, cached):
        with _openai_server(usage) as base_url:
            response = litellm.completion(
                model="gpt-4o",
                messages=[{"role": "user", "content": "hi"}],
                api_base=base_url,
                api_key="test-key",
            )
        costs.append(getattr(response, "_hidden_params", {}).get("response_cost"))

    plain_cost, cached_cost = costs
    assert plain_cost is not None and cached_cost is not None
    # Reconstructing a price locally would miss this discount entirely.
    assert cached_cost < plain_cost


def test_real_litellm_oneshot_reports_cost_and_token_details(monkeypatch):
    usage = {
        "prompt_tokens": 1200,
        "completion_tokens": 340,
        "total_tokens": 1540,
        "prompt_tokens_details": {
            "cached_tokens": 800,
            "cache_creation_tokens": 125,
        },
        "completion_tokens_details": {"reasoning_tokens": 120},
    }
    original_completion = litellm.completion
    with _openai_server(usage) as base_url:

        def routed_completion(**kwargs):
            return original_completion(
                **kwargs,
                api_base=base_url,
                api_key="test-key",
            )

        monkeypatch.setattr(litellm, "completion", routed_completion)
        result = run_litellm("Return Done.", "gpt-4o")

    (detail,) = result.usage_details
    assert detail["input_tokens"] == 1200
    assert detail["output_tokens"] == 340
    assert detail["cache_read_input_tokens"] == 800
    assert detail["cache_write_input_tokens"] == 125
    assert detail["reasoning_output_tokens"] == 120
    assert detail["costs"][0]["amount"] > 0
    assert detail["costs"][0]["source"] == "litellm.response_cost"


def test_real_litellm_agent_round_trip(monkeypatch, capsys, tmp_path):
    usage = {
        "prompt_tokens": 1200,
        "completion_tokens": 340,
        "total_tokens": 1540,
        "prompt_tokens_details": {
            "cached_tokens": 800,
            "cache_creation_tokens": 125,
        },
        "completion_tokens_details": {"reasoning_tokens": 120},
    }
    original_completion = litellm.completion
    with _openai_server(usage) as base_url:

        def routed_completion(**kwargs):
            return original_completion(
                **kwargs,
                api_base=base_url,
                api_key="test-key",
            )

        monkeypatch.setattr(litellm, "completion", routed_completion)
        monkeypatch.setattr(sys, "stdin", StringIO("Return Done."))
        monkeypatch.setattr(
            sys,
            "argv",
            [
                "litellm_agent.py",
                "--workspace",
                str(tmp_path),
                "--skills-dir",
                ".agents/skills",
                "--model",
                "gpt-4o",
                "--max-iterations",
                "1",
            ],
        )
        assert litellm_agent.main() == 0

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert [event["type"] for event in events] == ["request_usage", "response", "usage"]
    output = tmp_path / "output.jsonl"
    output.write_text("".join(json.dumps(event) + "\n" for event in events))

    backend = LiteLLMBackend(model="gpt-4o")
    _, legacy_in, legacy_out = backend.parse_output(str(output))
    usage_summary = backend.parse_usage(str(output), input_tokens=legacy_in, output_tokens=legacy_out)
    assert usage_summary.status == "complete"
    assert usage_summary.input_tokens == 1200
    assert usage_summary.output_tokens == 340
    assert usage_summary.cache_read_input_tokens == 800
    assert usage_summary.cache_write_input_tokens == 125
    assert usage_summary.reasoning_output_tokens == 120
    assert usage_summary.model_requests == 1
    assert usage_summary.costs[0].amount > 0
    assert usage_summary.costs[0].source == "litellm.response_cost"


def test_real_litellm_agent_disables_internal_retries(monkeypatch, capsys, tmp_path):
    usage = {"prompt_tokens": 10, "completion_tokens": 5, "total_tokens": 15}
    original_completion = litellm.completion
    request_state: dict[str, int] = {}
    with _openai_server(usage, transient_failures=1, request_state=request_state) as base_url:

        def routed_completion(**kwargs):
            return original_completion(
                **kwargs,
                api_base=base_url,
                api_key="test-key",
            )

        monkeypatch.setattr(litellm, "completion", routed_completion)
        monkeypatch.setattr(sys, "stdin", StringIO("Return Done."))
        monkeypatch.setattr(
            sys,
            "argv",
            [
                "litellm_agent.py",
                "--workspace",
                str(tmp_path),
                "--skills-dir",
                ".agents/skills",
                "--model",
                "gpt-4o",
                "--max-iterations",
                "1",
            ],
        )
        assert litellm_agent.main() == 1

    assert request_state["posts"] == 1
    events = [json.loads(line) for line in capsys.readouterr().out.splitlines() if line.lstrip().startswith("{")]
    assert [event["type"] for event in events] == ["error", "usage"]
    assert events[-1] == {
        "type": "usage",
        "input_tokens": 0,
        "output_tokens": 0,
        "model_requests": 1,
    }


def test_unpriceable_model_records_tokens_without_fabricating_a_cost(tmp_path):
    usage = {"prompt_tokens": 10, "completion_tokens": 5, "total_tokens": 15}
    with _openai_server(usage, model="totally-unknown-model-xyz") as base_url:
        response = litellm.completion(
            model="openai/totally-unknown-model-xyz",
            messages=[{"role": "user", "content": "hi"}],
            api_base=base_url,
            api_key="test-key",
        )

    event = _emit(response)

    assert event["input_tokens"] == 10
    assert event["output_tokens"] == 5
    # No price is available, so no cost is claimed — not a zero.
    assert "costs" not in event

    output = tmp_path / "output.jsonl"
    output.write_text(
        json.dumps(event)
        + "\n"
        + json.dumps({"type": "usage", "input_tokens": 10, "output_tokens": 5, "model_requests": 1})
        + "\n"
    )
    usage_summary = LiteLLMBackend(model="openai/totally-unknown-model-xyz").parse_usage(
        str(output),
        input_tokens=10,
        output_tokens=5,
    )
    assert usage_summary.status == "lower_bound"
    assert usage_summary.costs == ()
    assert "LiteLLM cost is unavailable for 1 model request(s); total is a lower bound" in usage_summary.warnings
