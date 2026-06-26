"""Regression tests for parse_strict_status — the tlapm --strict interpreter.

The bug this LOCKS (fixed in 1a545f0): `tlapm --strict` reports a benchmark's
GIVEN admitted lemmas (an L1 preceding `PROOF OMITTED`) as module-wide "omitted"
and exits 11, so a *correct* L1 solution (target fully proved, given lemma still
OMITTED) must NOT be graded as incomplete. Only a MISSING step (no proof at all
— bare QED, unproven helper lemma, unfinished target) is a real agent gap.

Run: PYTHONPATH=src python3 -m pytest tests/common/test_strict_status.py
(or:  PYTHONPATH=src python3 tests/common/test_strict_status.py)
"""

from common.check_proof import parse_strict_status

# Real `tlapm --strict` output shapes.
CLEAN = "File ...\n[INFO]: All 9 obligations proved."

# A CORRECT L1 solution: the target is fully proved, but the benchmark's GIVEN
# `THEOREM Cantor ... PROOF OMITTED` lemma remains — so --strict exits 11 with
# "0 missing, 1 omitted". This must still count as complete.
L1_GIVEN_OMITTED = (
    '[ERROR]: Proof incomplete in module "Cantor10_NoSetContainsAllValues": '
    "0 missing, 1 omitted proof step(s).\n"
    "[INFO]: All 9 obligations proved."
)

# Agent left a gap: a bare QED / unproven helper lemma (no proof keyword) = MISSING.
MISSING_STEP = (
    '[ERROR]: Proof incomplete in module "X": 1 missing, 0 omitted proof step(s).\n[INFO]: All 1 obligation proved.'
)

FAILED_OBLIGATION = "[ERROR]: 1/3 obligations failed."


def test_clean_run_is_complete():
    complete, n_missing, failed = parse_strict_status(0, CLEAN)
    assert complete
    assert n_missing == 0
    assert not failed


def test_given_omitted_lemma_still_passes():
    # THE regression: exit 11 whose only gap is a GIVEN omitted lemma -> complete.
    complete, n_missing, failed = parse_strict_status(11, L1_GIVEN_OMITTED)
    assert complete, "a correct L1 solution keeping a given PROOF OMITTED lemma must PASS"
    assert n_missing == 0
    assert not failed


def test_missing_step_fails():
    complete, n_missing, failed = parse_strict_status(11, MISSING_STEP)
    assert not complete, "a missing (no-proof) step is a real agent gap"
    assert n_missing == 1


def test_failed_obligation_fails():
    complete, _n_missing, failed = parse_strict_status(10, FAILED_OBLIGATION)
    assert not complete
    assert failed


def test_timeout_or_error_exit_not_complete():
    complete, _n_missing, _failed = parse_strict_status(-1, "TIMEOUT after 600s")
    assert not complete


if __name__ == "__main__":
    for _name, _fn in sorted(globals().items()):
        if _name.startswith("test_") and callable(_fn):
            _fn()
            print(f"ok  {_name}")
    print("all passed")
