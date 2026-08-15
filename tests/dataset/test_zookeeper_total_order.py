"""Lock ZooKeeper TotalOrder so a singleton <<b>> log is a miss.

The Remix/Zab comment is: if some follower delivers a before b, any process
that delivers b must also deliver a before b. The old encoding required
``committed2 >= 2``, which skips a process whose log is only ``<<b>>``.
The witness still needs ``committed1 >= 2`` (two entries to have a before b).
"""

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


def test_total_order_does_not_skip_singleton_delivery_of_b():
    for path in TOTAL_ORDER_FILES:
        body = _total_order_body(path.read_text(encoding="utf-8"))
        assert WITNESS_GUARD in body, f"{path} dropped the two-entry witness guard"
        assert OTHER_GUARD not in body, f"{path} still skips a process with lastCommitted index 1"


def test_total_order_fails_when_other_process_delivered_only_b():
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
