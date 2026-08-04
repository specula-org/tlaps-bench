"""In-container LiteLLM agent usage emission."""

from __future__ import annotations

import io
import json
import sys
from types import SimpleNamespace

import pytest

from evaluator.backends.litellm import LiteLLMBackend

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


def test_nonfinite_hidden_cost_is_omitted(capsys):
    response = _FakeResponse(
        usage=_usage(prompt_tokens=10, completion_tokens=5),
        hidden={"response_cost": float("inf")},
    )

    event = _emit(capsys, response)

    assert "costs" not in event


def test_missing_hidden_cost_is_omitted(capsys):
    response = _FakeResponse(usage=_usage(prompt_tokens=10, completion_tokens=5))

    event = _emit(capsys, response)

    assert "costs" not in event


def test_cache_and_reasoning_details_are_emitted(capsys):
    response = _FakeResponse(
        usage=_usage(
            prompt_tokens=100,
            completion_tokens=40,
            prompt_tokens_details=SimpleNamespace(cached_tokens=30, cache_creation_tokens=12),
            completion_tokens_details=SimpleNamespace(reasoning_tokens=15),
        ),
        hidden={"response_cost": 0.001},
    )

    event = _emit(capsys, response)

    assert event["cache_read_input_tokens"] == 30
    assert event["cache_write_input_tokens"] == 12
    assert event["reasoning_output_tokens"] == 15


def test_absent_token_fields_are_omitted_not_zeroed(capsys):
    response = _FakeResponse(usage=_usage(prompt_tokens=None, completion_tokens=7), hidden={"response_cost": 0.0})

    event = _emit(capsys, response)

    assert "input_tokens" not in event
    assert event["output_tokens"] == 7
    # An explicit zero cost is still an exact value.
    assert event["costs"] == [{"amount": 0.0, "unit": "usd", "source": "litellm.response_cost"}]


def test_response_without_usage_still_emits_request_evidence(capsys):
    event = _emit(capsys, _FakeResponse(usage=None))

    assert event["type"] == "request_usage"
    assert event["iteration"] == 1
    assert event["request_id"] == "chatcmpl-1"
    assert "input_tokens" not in event
    assert "output_tokens" not in event
    assert "costs" not in event


def test_agent_can_finish_a_response_without_usage(monkeypatch, capsys):
    message = SimpleNamespace(
        content="done",
        tool_calls=None,
        model_dump=lambda: {"role": "assistant", "content": "done"},
    )
    response = SimpleNamespace(
        usage=None,
        model="unknown/model",
        id="chatcmpl-no-usage",
        choices=[SimpleNamespace(finish_reason="stop", message=message)],
    )
    monkeypatch.setattr(litellm_agent.litellm, "completion", lambda **_: response)
    monkeypatch.setattr(sys, "stdin", io.StringIO("prove this"))
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "litellm_agent.py",
            "--workspace",
            ".",
            "--skills-dir",
            ".agents/skills",
            "--model",
            "unknown/model",
            "--max-iterations",
            "1",
        ],
    )

    assert litellm_agent.main() == 0

    events = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    request_usage = next(event for event in events if event["type"] == "request_usage")
    aggregate = next(event for event in events if event["type"] == "usage")
    assert "input_tokens" not in request_usage
    assert "output_tokens" not in request_usage
    assert aggregate == {
        "type": "usage",
        "input_tokens": 0,
        "output_tokens": 0,
        "model_requests": 1,
    }


def test_first_request_lists_skill_metadata_without_eagerly_loading_bodies(monkeypatch, tmp_path):
    skills_root = tmp_path / ".agents" / "skills"
    alpha = skills_root / "alpha-skill" / "SKILL.md"
    zeta = skills_root / "zeta-skill" / "SKILL.md"
    alpha.parent.mkdir(parents=True)
    zeta.parent.mkdir(parents=True)
    alpha.write_text(
        "---\nname: alpha-skill\ndescription: Use when alpha guidance is relevant.\n---\n\nALPHA_FULL_INSTRUCTIONS\n"
    )
    zeta.write_text(
        "---\nname: zeta-skill\ndescription: Use when zeta guidance is relevant.\n---\n\nZETA_FULL_INSTRUCTIONS\n"
    )
    message = SimpleNamespace(
        content="done",
        tool_calls=None,
        model_dump=lambda: {"role": "assistant", "content": "done"},
    )
    response = SimpleNamespace(
        usage=None,
        model="unknown/model",
        id="chatcmpl-skills",
        choices=[SimpleNamespace(finish_reason="stop", message=message)],
    )
    completion_calls = []

    def fake_completion(**options):
        completion_calls.append(options)
        return response

    monkeypatch.setattr(litellm_agent.litellm, "completion", fake_completion)
    monkeypatch.setattr(sys, "stdin", io.StringIO("prove this"))
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
            "unknown/model",
            "--max-iterations",
            "1",
        ],
    )

    assert litellm_agent.main() == 0

    prompt = completion_calls[0]["messages"][0]["content"]
    assert prompt.startswith("prove this")
    assert "Use when alpha guidance is relevant." in prompt
    assert "Use when zeta guidance is relevant." in prompt
    assert ".agents/skills/alpha-skill/SKILL.md" in prompt
    assert ".agents/skills/zeta-skill/SKILL.md" in prompt
    assert prompt.index("<name>alpha-skill</name>") < prompt.index("<name>zeta-skill</name>")
    assert "ALPHA_FULL_INSTRUCTIONS" not in prompt
    assert "ZETA_FULL_INSTRUCTIONS" not in prompt
    assert (
        litellm_agent.exec_tool(
            "read_file",
            {"path": ".agents/skills/alpha-skill/SKILL.md"},
            str(tmp_path),
        )
        == alpha.read_text()
    )


def test_backend_passes_its_project_skills_directory_to_agent():
    backend = LiteLLMBackend(model="unknown/model")

    command = backend.build_command("/workspace", "/results")

    skills_option = command.index("--skills-dir")
    assert command[skills_option + 1] == backend.project_skills_dir


def test_request_usage_is_flushed_immediately(monkeypatch):
    calls = []

    def capture_print(*args, **kwargs):
        calls.append((args, kwargs))

    monkeypatch.setattr("builtins.print", capture_print)
    response = _FakeResponse(
        usage=_usage(prompt_tokens=1, completion_tokens=1),
        hidden={"response_cost": 0.01},
    )

    litellm_agent._emit_request_usage(response, 1, 0.5)

    assert len(calls) == 1
    assert calls[0][1]["flush"] is True


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
