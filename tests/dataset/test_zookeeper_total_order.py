"""Lock ZooKeeper's pre-initialized history and original TotalOrder guard."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]

TOTAL_ORDER_FILES = (
    REPO_ROOT / "source" / "ZooKeeper" / "Zab.tla",
    REPO_ROOT / "source" / "ZooKeeper_LowLevel" / "ZkV3_7_0.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper" / "Zab_TotalOrderDefs.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper_LowLevel" / "ZkV3_7_0_TotalOrderDefs.tla",
)

HIGH_LEVEL_MODELS = (
    REPO_ROOT / "source" / "ZooKeeper" / "Zab.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper" / "ZabModel.tla",
)

LOW_LEVEL_MODELS = (
    REPO_ROOT / "source" / "ZooKeeper_LowLevel" / "ZkV3_7_0.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper_LowLevel" / "ZkV3_7_0Model.tla",
)

LOW_LEVEL_ELECTION_FILES = (
    REPO_ROOT / "source" / "ZooKeeper_LowLevel" / "FastLeaderElection.tla",
    *(REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper_LowLevel").glob("ZkV3_7_0_*/FastLeaderElection.tla"),
)

WITNESS_GUARD = "committed1 >= 2"
OTHER_GUARD = "committed2 >= 2"

TLC_MODULE = REPO_ROOT / "tests" / "dataset" / "TotalOrderQuantifierCheck.tla"
TLC_CONFIG = REPO_ROOT / "tests" / "dataset" / "TotalOrderQuantifierCheck.cfg"
TLA2TOOLS = REPO_ROOT / "lib" / "tla2tools.jar"


def _total_order_body(text: str) -> str:
    start = text.index("TotalOrder ==")
    rest = text[start:]
    ends = []
    for marker in ("\nTHEOREM ", "\n===="):
        idx = rest.find(marker)
        if idx != -1:
            ends.append(idx)
    return rest[: min(ends)] if ends else rest


def _compact(text: str) -> str:
    return " ".join(text.split())


def test_total_order_keeps_original_two_log_guard():
    for path in TOTAL_ORDER_FILES:
        body = _total_order_body(path.read_text(encoding="utf-8"))
        assert WITNESS_GUARD in body, f"{path} dropped the two-entry witness guard"
        assert OTHER_GUARD in body, f"{path} dropped the initialized-log guard"


def test_zookeeper_starts_with_a_committed_bootstrap_prefix():
    for path in HIGH_LEVEL_MODELS:
        text = _compact(path.read_text(encoding="utf-8"))
        assert r"history = [s \in Server |-> <<BootstrapTxn>>]" in text, path
        assert r"lastCommitted = [s \in Server |-> [ index |-> 1," in text, path
        assert "proposalMsgsLog = BootstrapProposalMsgs" in text, path

    for path in LOW_LEVEL_MODELS:
        text = _compact(path.read_text(encoding="utf-8"))
        assert r"lastCommitted = [s \in Server |-> [ index |-> 1," in text, path
        assert r"initialHistory = [s \in Server |-> <<BootstrapTxn>>]" in text, path
        assert "proposalMsgsLog = BootstrapProposalMsgs" in text, path

    assert len(LOW_LEVEL_ELECTION_FILES) == 10
    for path in LOW_LEVEL_ELECTION_FILES:
        text = _compact(path.read_text(encoding="utf-8"))
        assert r"history = [s \in Server |-> <<BootstrapTxn>>]" in text, path
        assert r"lastProcessed = [s \in Server |-> [index |-> 1," in text, path


def test_total_order_catches_b_without_a_after_bootstrap():
    java = shutil.which("java")
    if java is None:
        pytest.skip("java is required to evaluate the TotalOrder TLC fixture")
    if not TLA2TOOLS.is_file():
        pytest.skip(f"missing {TLA2TOOLS}")

    result = subprocess.run(
        [
            java,
            "-XX:+UseParallelGC",
            "-cp",
            str(TLA2TOOLS),
            "tlc2.TLC",
            "-deadlock",
            "-nowarning",
            "-config",
            str(TLC_CONFIG),
            str(TLC_MODULE),
        ],
        check=False,
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        env={**os.environ, "JAVA_TOOL_OPTIONS": ""},
    )
    output = result.stdout + result.stderr
    assert result.returncode == 0, output
    assert "No error has been found" in output
    assert "Assumption" not in output
