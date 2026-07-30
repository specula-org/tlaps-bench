from pathlib import Path

import pytest

from dataset.proof_completion.generate import _run_duplicate_gate

TASK = """---- MODULE Sets_Test ----
THEOREM Test == TRUE
PROOF OBVIOUS
====
"""


def _write_task(root: Path, group: str, name: str = "Sets_Test.tla", content: str = TASK) -> Path:
    path = root / group / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


@pytest.mark.parametrize(
    ("name", "canonical", "copies"),
    [
        ("Sets_Test.tla", "Data", ("Consensus",)),
        (
            "Channel_proof_Test.tla",
            "tlaplus_examples_SpecifyingSystems_AsynchronousInterface",
            (
                "tlaplus_examples_SpecifyingSystems_Composing",
                "tlaplus_examples_SpecifyingSystems_FIFO",
            ),
        ),
        (
            "HourClock_proof_Test.tla",
            "tlaplus_examples_SpecifyingSystems_HourClock",
            (
                "tlaplus_examples_SpecifyingSystems_Composing",
                "tlaplus_examples_SpecifyingSystems_Liveness",
                "tlaplus_examples_SpecifyingSystems_RealTime",
            ),
        ),
        (
            "InternalMemory_proof_Test.tla",
            "tlaplus_examples_SpecifyingSystems_CachingMemory",
            (
                "tlaplus_examples_SpecifyingSystems_Composing",
                "tlaplus_examples_SpecifyingSystems_Liveness",
                "tlaplus_examples_SpecifyingSystems_RealTime",
            ),
        ),
    ],
)
def test_duplicate_gate_drops_approved_copies(tmp_path, name, canonical, copies):
    keeper = _write_task(tmp_path, canonical, name=name)
    duplicates = [_write_task(tmp_path, copy, name=name) for copy in copies]

    removed = _run_duplicate_gate(str(tmp_path))

    assert removed == [str(path) for path in duplicates]
    assert keeper.exists()
    assert all(not path.exists() for path in duplicates)


def test_duplicate_gate_rejects_unknown_group_without_deleting(tmp_path):
    first = _write_task(tmp_path, "Data")
    second = _write_task(tmp_path, "Consensus")
    third = _write_task(tmp_path, "Unknown")

    with pytest.raises(RuntimeError, match="unapproved exact-byte group"):
        _run_duplicate_gate(str(tmp_path))

    assert first.exists()
    assert second.exists()
    assert third.exists()


def test_duplicate_gate_keeps_nonidentical_targets(tmp_path):
    first = _write_task(tmp_path, "Data")
    second = _write_task(tmp_path, "Consensus", content=TASK + "\n")

    assert _run_duplicate_gate(str(tmp_path)) == []
    assert first.exists()
    assert second.exists()
