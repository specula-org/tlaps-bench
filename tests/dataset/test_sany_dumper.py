"""Regression tests for the SANY semantic dependency dump."""

from dataset.proof_from_scratch.generate import compute_reachable, dump_sany


def test_named_operator_argument_is_reachable(tmp_path):
    source = tmp_path / "OperatorArgument.tla"
    source.write_text(
        """------------------------- MODULE OperatorArgument -------------------------
EXTENDS Sequences

CONSTANT Items

Keep(item) == TRUE
Filtered == SelectSeq(Items, Keep)

THEOREM Goal == Filtered = Filtered
PROOF OBVIOUS
=============================================================================
"""
    )

    dump = dump_sany(str(source))
    filtered = next(op for op in dump["operators"] if op["name"] == "Filtered")
    target = next(theorem for theorem in dump["theorems"] if theorem["name"] == "Goal")

    assert filtered["references"] == ["Keep"]
    assert {"Filtered", "Keep"} <= compute_reachable(dump, target)
