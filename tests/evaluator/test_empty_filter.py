"""The runner rejects an empty task selection before performing setup work."""

import sys
from unittest.mock import MagicMock

import pytest

from evaluator import runner
from evaluator.modes.base import Mode


class EmptyMode:
    name = "proof-completion"

    def get_benchmark_files(self, filter_pattern=None):
        return []

    def benchmark_dir(self):
        return "/benchmarks/proof-completion"


class FixtureMode(Mode):
    name = "test"


def test_empty_filter_fails_before_auth_image_or_preflight(monkeypatch, capsys):
    backend = MagicMock()
    monkeypatch.setattr(runner, "get_backend", lambda *args, **kwargs: backend)
    monkeypatch.setattr(runner, "get_mode", lambda *args, **kwargs: EmptyMode())
    ensure_image = MagicMock()
    preflight = MagicMock()
    monkeypatch.setattr(runner, "ensure_image", ensure_image)
    monkeypatch.setattr(runner, "_run_preflight", preflight)
    monkeypatch.setattr(sys, "argv", ["tlaps-bench run", "--filter", "typo"])

    with pytest.raises(SystemExit) as exc_info:
        runner.main()

    assert exc_info.value.code == 2
    stderr = capsys.readouterr().err
    assert "no benchmarks matched --filter 'typo'" in stderr
    assert "usage:" not in stderr
    backend.check_auth.assert_not_called()
    ensure_image.assert_not_called()
    preflight.assert_not_called()


def test_empty_comma_filter_does_not_match_every_benchmark(tmp_path):
    benchmark_dir = tmp_path / "test" / "Example"
    benchmark_dir.mkdir(parents=True)
    (benchmark_dir / "Example_Theorem.tla").write_text(
        "---- MODULE Example_Theorem ----\nTHEOREM Theorem == TRUE PROOF OBVIOUS\n====\n"
    )
    mode = FixtureMode(str(tmp_path), "/checker")

    assert mode.get_benchmark_files("missing,") == []
