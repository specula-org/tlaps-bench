"""Unit coverage for check_proof fingerprint-cache flags."""

import os
from pathlib import Path

import pytest

from common import check_proof
from evaluator.modes import get_mode, list_modes

NO_CACHE_FLAG = "--no-cache"


def test_cache_args_default_reuses_beside_target(tmp_path):
    args = check_proof.tlapm_cache_args(str(tmp_path), no_cache=False)
    assert args == ["--cache-dir", str(tmp_path / ".tlacache"), "--safefp"]


def test_cache_args_no_cache_gives_nothing(tmp_path):
    assert check_proof.tlapm_cache_args(str(tmp_path), no_cache=True) == []


@pytest.mark.parametrize("mode_name", list_modes())
def test_grader_command_always_passes_no_cache(mode_name, tmp_path):
    mode = get_mode(mode_name, str(tmp_path), "/usr/local/bin/check_proof_bin")
    cmd = mode.checker_command("/ws", "Foo.tla", "/out/check.result", 600)
    assert NO_CACHE_FLAG in cmd, f"grader command for {mode_name} would reuse the agent's cache"


def _src(rel):
    return (Path(__file__).resolve().parents[2] / "src" / rel).read_text(encoding="utf-8")


def test_no_cache_flag_coupled_between_grader_and_checker():
    assert NO_CACHE_FLAG in _src(os.path.join("evaluator", "modes", "base.py"))
    assert f'"{NO_CACHE_FLAG}"' in _src(os.path.join("common", "check_proof.py"))


if __name__ == "__main__":
    import sys

    sys.exit(pytest.main([__file__, "-q"]))
