"""Evaluator SANY preflight tests."""

import subprocess

import pytest

from evaluator import runner


def test_native_sany_preflight_accepts_structured_valid_status(monkeypatch):
    calls = []

    def completed(command, **kwargs):
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 0, stdout="SANY-STATUS: valid\nSANY OK\n", stderr="")

    monkeypatch.setattr(subprocess, "run", completed)

    runner._run_sany_preflight(use_container=False, container_image="unused")

    assert len(calls) == 1
    assert "--sany-only" in calls[0][0]


@pytest.mark.parametrize(
    ("returncode", "stdout"),
    [
        (3, "SANY-STATUS: unavailable\n"),
        (0, "SANY OK without structured status\n"),
    ],
)
def test_native_sany_preflight_fails_closed(monkeypatch, returncode, stdout):
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda command, **_kwargs: subprocess.CompletedProcess(command, returncode, stdout=stdout, stderr="broken"),
    )

    with pytest.raises(RuntimeError, match="SANY preflight failed"):
        runner._run_sany_preflight(use_container=False, container_image="unused")
