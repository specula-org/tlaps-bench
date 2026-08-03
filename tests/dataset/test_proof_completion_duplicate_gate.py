import sys
from pathlib import Path

import pytest

from dataset.proof_completion import generate
from dataset.proof_completion.generate import _drop_detail, _run_duplicate_gate

TASK = """---- MODULE Sets_Test ----
THEOREM Test == TRUE
PROOF OBVIOUS
====
"""

TASK_WITH_DEPENDENCY = """---- MODULE Sets_Test ----
EXTENDS Mid
THEOREM Test == TRUE
PROOF OBVIOUS
====
"""


def _write_task(root: Path, group: str, name: str = "Sets_Test.tla", content: str = TASK) -> Path:
    path = root / group / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


def _write_module(root: Path, group: str, name: str, content: str) -> Path:
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
    orphan = _write_module(tmp_path, "Orphan", "Orphan.tla", "---- MODULE Orphan ----\n====\n")

    with pytest.raises(RuntimeError, match="unapproved exact-byte group"):
        _run_duplicate_gate(str(tmp_path))

    assert first.exists()
    assert second.exists()
    assert third.exists()
    assert orphan.exists()


def test_duplicate_gate_keeps_nonidentical_targets(tmp_path):
    first = _write_task(tmp_path, "Data")
    second = _write_task(tmp_path, "Consensus", content=TASK + "\n")

    assert _run_duplicate_gate(str(tmp_path)) == []
    assert first.exists()
    assert second.exists()


def test_duplicate_gate_prunes_only_unreferenced_dependencies(tmp_path):
    keeper = _write_task(tmp_path, "Data", content=TASK_WITH_DEPENDENCY)
    duplicate = _write_task(tmp_path, "Consensus", content=TASK_WITH_DEPENDENCY)

    mid = "---- MODULE Mid ----\nEXTENDS Leaf\n====\n"
    leaf = "---- MODULE Leaf ----\nINSTANCE Mid\n====\n"
    unused = "---- MODULE Unused ----\n====\n"
    for group in ("Data", "Consensus"):
        _write_module(tmp_path, group, "Mid.tla", mid)
        _write_module(tmp_path, group, "Leaf.tla", leaf)
        _write_module(tmp_path, group, "Unused.tla", unused)

    removed = _run_duplicate_gate(str(tmp_path))

    assert removed == [str(duplicate)]
    assert keeper.exists()
    assert (tmp_path / "Data" / "Mid.tla").exists()
    assert (tmp_path / "Data" / "Leaf.tla").exists()
    assert not (tmp_path / "Data" / "Unused.tla").exists()
    assert not (tmp_path / "Consensus").exists()


def test_drop_detail_omits_all_zero_counts():
    assert _drop_detail(10, 0, 0) == ""
    assert _drop_detail(10, 1, 0) == " (10 generated, 1 duplicates and 0 degenerate tasks dropped)"
    assert _drop_detail(10, 0, 1) == " (10 generated, 0 duplicates and 1 degenerate tasks dropped)"


@pytest.mark.parametrize("shared_model", [False, True])
def test_main_omits_all_zero_drop_detail(monkeypatch, capsys, tmp_path, shared_model):
    monkeypatch.setattr(generate, "BENCHMARK_DIR", str(tmp_path))
    monkeypatch.setattr(generate, "generate_shared_model_l1", lambda output_root: 1)
    monkeypatch.setattr(generate, "find_source_dirs", lambda: [])
    monkeypatch.setattr(generate, "_run_duplicate_gate", lambda directory: [])
    monkeypatch.setattr(generate, "_run_sany_gate", lambda directory: 0)
    monkeypatch.setattr(generate, "_prune_unreferenced_dependencies", lambda directory: [])
    argv = ["generate.py", "--shared-model"] if shared_model else ["generate.py"]
    monkeypatch.setattr(sys, "argv", argv)

    generate.main()

    output = capsys.readouterr().out
    assert "0 duplicates" not in output
    assert "0 degenerate tasks" not in output
