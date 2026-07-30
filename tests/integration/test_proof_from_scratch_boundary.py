"""End-to-end proof-from-scratch editable-region acceptance."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
)

REPO = Path(__file__).resolve().parents[2]
CHECKER = REPO / "src" / "common" / "check_proof.py"
SANY_RUN_SH = REPO / "src" / "dataset" / "sany-dump" / "run.sh"


def _tlapm() -> str:
    for candidate in (Path("/opt/tlapm/bin/tlapm"), Path.home() / ".tlapm" / "bin" / "tlapm"):
        if candidate.is_file():
            return str(candidate)
    pytest.skip("tlapm is not installed")


def _task(*, helper: str = "", proof: str = "PROOF OBVIOUS") -> str:
    return "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            BEGIN_AGENT_HELPERS,
            helper,
            END_AGENT_HELPERS,
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            proof,
            END_AGENT_PROOF,
            "====",
            "",
        )
    )


def _run_checker(tmp_path: Path, submitted: str) -> subprocess.CompletedProcess[str]:
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir(parents=True)
    workspace.mkdir()
    model = "---- MODULE Model ----\n====\n"
    (canonical / "Task.tla").write_text(_task())
    (canonical / "Model.tla").write_text(model)
    (workspace / "Task.tla").write_text(submitted)
    (workspace / "Model.tla").write_text(model)

    env = {
        **os.environ,
        "PYTHONPATH": str(REPO / "src"),
        "SANY_RUN_SH": str(SANY_RUN_SH),
    }
    return subprocess.run(
        [
            sys.executable,
            str(CHECKER),
            str(workspace / "Task.tla"),
            "--mode",
            "proof-from-scratch",
            "--no-container",
            "--no-git-track",
            "--no-cache",
            "--canonical-replay-required",
            "--benchmark-dir",
            str(canonical),
            "--tlapm",
            _tlapm(),
        ],
        capture_output=True,
        text=True,
        timeout=120,
        env=env,
    )


def test_real_checker_accepts_helpers_and_rejects_forbidden_declaration(tmp_path):
    valid = _run_checker(
        tmp_path / "valid",
        _task(
            helper="Fresh == TRUE\nLEMMA Helper == TRUE\nPROOF OBVIOUS",
            proof="PROOF BY Helper",
        ),
    )

    assert valid.returncode == 0, valid.stdout + valid.stderr
    assert "PASS — target goal genuinely proved" in valid.stdout

    invalid = _run_checker(
        tmp_path / "invalid",
        _task(helper="CONSTANT C"),
    )

    assert invalid.returncode == 1, invalid.stdout + invalid.stderr
    assert "HELPER_REGION_VIOLATION" in invalid.stdout
    assert "CHEAT-DETECTED: editable_regions_valid" in invalid.stdout
