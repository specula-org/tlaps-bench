"""Reference-proof step counting for Proof Completion."""

from dataset.proof_completion.reference_steps import (
    count_reference_proof_steps,
    reference_proof_steps_for_name,
)


def test_count_reference_proof_steps_ignores_comments_and_direct_proofs():
    assert count_reference_proof_steps(["BY DEF Foo"]) == 0
    assert count_reference_proof_steps(["<1>1. TRUE", "  <2>1. TRUE", "<1> QED"]) == 3
    assert count_reference_proof_steps(["\\* <1>1. commented", "(*", "<1>2. also commented", "*)", "<1>1. real"]) == 1


def test_reference_proof_steps_for_name_returns_none_for_obvious():
    lines = [
        "---- MODULE M ----",
        "THEOREM CompleteSafety == TRUE",
        "PROOF OBVIOUS",
        "====",
    ]
    assert reference_proof_steps_for_name(lines, "CompleteSafety") is None


def test_reference_proof_steps_for_name_counts_structured_and_direct():
    lines = [
        "---- MODULE M ----",
        "LEMMA Direct == TRUE",
        "BY DEF Direct",
        "THEOREM Structured == TRUE",
        "<1>1. TRUE",
        "<1> QED",
        "====",
    ]
    assert reference_proof_steps_for_name(lines, "Direct") == 0
    assert reference_proof_steps_for_name(lines, "Structured") == 2
