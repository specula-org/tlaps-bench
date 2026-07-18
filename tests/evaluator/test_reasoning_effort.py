"""Reasoning-effort CLI plumbing across evaluator backends."""

import pytest

from evaluator.backends import get_backend


def _has_option(command: list[str], option: str, value: str) -> bool:
    return any(command[index : index + 2] == [option, value] for index in range(len(command) - 1))


@pytest.mark.parametrize(
    ("backend_name", "option", "value"),
    [
        ("codex", "-c", "model_reasoning_effort=low"),
        ("claude_code", "--effort", "low"),
        ("copilot", "--effort", "low"),
        ("litellm", "--reasoning-effort", "low"),
        ("copilot_oneshot", "--reasoning-effort", "low"),
        ("litellm_oneshot", "--reasoning-effort", "low"),
    ],
)
def test_explicit_reasoning_effort_reaches_backend_command(backend_name, option, value):
    backend = get_backend(backend_name, model="test-model")
    backend.set_reasoning_effort("low")

    command = backend.build_command("/workspace", "/results")

    assert _has_option(command, option, value)
    assert backend.initial_result_metadata()["reasoning_effort"] == "low"


def test_omitted_reasoning_effort_preserves_existing_defaults():
    codex = get_backend("codex")
    claude = get_backend("claude_code")
    copilot = get_backend("copilot")
    litellm = get_backend("litellm")
    litellm_oneshot = get_backend("litellm_oneshot")

    assert not any(value.startswith("model_reasoning_effort=") for value in codex.build_command("/w", "/r"))
    assert _has_option(claude.build_command("/w", "/r"), "--effort", "max")
    assert _has_option(copilot.build_command("/w", "/r"), "--effort", "max")
    assert "--reasoning-effort" not in litellm.build_command("/w", "/r")
    assert "--reasoning-effort" not in litellm_oneshot.build_command("/w", "/r")
    assert "reasoning_effort" not in codex.initial_result_metadata()


def test_backend_specific_reasoning_effort_validation():
    with pytest.raises(ValueError, match="does not support --reasoning-effort"):
        get_backend("pi").set_reasoning_effort("low")
