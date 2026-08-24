"""Docker grader uses the same frozen official library catalog as the runner."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from common.proof_from_scratch_contract import (
    BEGIN_AGENT_HELPERS,
    BEGIN_AGENT_PROOF,
    END_AGENT_HELPERS,
    END_AGENT_PROOF,
)
from common.proof_libraries import CATALOG_FILENAME, scan_official_libraries

REPO = Path(__file__).resolve().parents[2]
HAS_IMAGE = (
    subprocess.run(
        ["docker", "image", "inspect", "tlaps-bench-base:latest"],
        capture_output=True,
    ).returncode
    == 0
    if shutil.which("docker")
    else False
)


@pytest.mark.skipif(not HAS_IMAGE, reason="tlaps-bench-base:latest is not built")
def test_docker_grader_resolves_dynamic_official_library_imports(tmp_path):
    canonical = tmp_path / "canonical"
    workspace = tmp_path / "workspace"
    canonical.mkdir()
    workspace.mkdir()
    model = "---- MODULE Model ----\n====\n"
    task = "\n".join(
        (
            "---- MODULE Task ----",
            "EXTENDS Model",
            BEGIN_AGENT_HELPERS,
            "LOCAL NatLib == INSTANCE NaturalsInduction",
            "LOCAL FiniteLib == INSTANCE FiniteSetTheorems",
            "LOCAL WFLib == INSTANCE WellFoundedInduction",
            "LEMMA LibrariesResolve == TRUE",
            "<1>1. USE NatLib!NatInduction",
            "<1>2. USE FiniteLib!FS_Induction",
            "<1>3. USE WFLib!WFInduction",
            "<1>4. QED OBVIOUS",
            END_AGENT_HELPERS,
            "THEOREM Target == TRUE",
            BEGIN_AGENT_PROOF,
            "PROOF OBVIOUS",
            END_AGENT_PROOF,
            "====",
            "",
        )
    )
    canonical_task = task.replace(
        "LOCAL NatLib == INSTANCE NaturalsInduction\n"
        "LOCAL FiniteLib == INSTANCE FiniteSetTheorems\n"
        "LOCAL WFLib == INSTANCE WellFoundedInduction\n"
        "LEMMA LibrariesResolve == TRUE\n"
        "<1>1. USE NatLib!NatInduction\n"
        "<1>2. USE FiniteLib!FS_Induction\n"
        "<1>3. USE WFLib!WFInduction\n"
        "<1>4. QED OBVIOUS\n",
        "",
    )
    (canonical / "Task.tla").write_text(canonical_task)
    (canonical / "Model.tla").write_text(model)
    (canonical / CATALOG_FILENAME).write_bytes(scan_official_libraries().to_bytes())
    (workspace / "Task.tla").write_text(task)
    (workspace / "Model.tla").write_text(model)

    result = subprocess.run(
        [
            "uv",
            "run",
            "tlaps-bench",
            "check",
            str(workspace / "Task.tla"),
            "--mode",
            "proof-from-scratch",
            "--container",
            "--no-git-track",
            "--no-cache",
            "--benchmark-dir",
            str(canonical),
            "--timeout",
            "120",
        ],
        capture_output=True,
        text=True,
        timeout=180,
        cwd=REPO,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert "PASS — target goal genuinely proved" in result.stdout
