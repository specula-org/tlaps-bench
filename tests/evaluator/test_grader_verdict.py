"""The runner relabels a cheat-type FAIL as CHEATING for the human-facing report.

Guards the merge-integration seam: the merged checker is binary (exit 0 = PASS,
1 = FAIL — no exit code 2), so the CHEATING display verdict is reconstructed in
the runner from the checker's CHEAT-DETECTED marker. Without this, a cheat and an
honest incomplete proof both render as a plain FAIL.

Run: PYTHONPATH=src python3 -m pytest tests/evaluator/test_grader_verdict.py
(or:  PYTHONPATH=src python3 tests/evaluator/test_grader_verdict.py)
"""

from evaluator.runner import _parse_grader_result


def test_pass():
    r = {}
    _parse_grader_result(0, "SANY-STATUS: valid\nVERDICT\n  PASS — target goal genuinely proved\n", r)
    assert r["check_verdict"] == "PASS"
    assert r["sany_status"] == "valid"
    assert r["sany_valid"] is True


def test_cheat_fail_relabelled_to_cheating():
    out = (
        "SANY-STATUS: valid\n  FAIL\n  GATES-FAILED: A:identity\n  CHEAT-DETECTED: no_extra_axiom,statement_unchanged\n"
    )
    r = {}
    _parse_grader_result(1, out, r)
    assert r["check_verdict"] == "CHEATING"
    assert r["cheat_checks"] == ["no_extra_axiom", "statement_unchanged"]
    assert r["failed_gates"] == ["A:identity"]


def test_honest_incomplete_stays_fail():
    # FAIL with no integrity check failing (no CHEAT-DETECTED) → plain FAIL.
    r = {}
    _parse_grader_result(1, "SANY-STATUS: valid\n  FAIL\n  GATES-FAILED: B:discharge\n", r)
    assert r["check_verdict"] == "FAIL"
    assert "cheat_checks" not in r


def test_admitted_goal_is_cheating_even_under_gate_b():
    # An admitted goal lives under gate B (with honest completion checks) but is a
    # cheat: the CHEAT-DETECTED marker carries it, so it relabels to CHEATING.
    out = "SANY-STATUS: valid\n  FAIL\n  GATES-FAILED: B:discharge\n  CHEAT-DETECTED: no_admitted_goal\n"
    r = {}
    _parse_grader_result(1, out, r)
    assert r["check_verdict"] == "CHEATING"


def test_sany_invalid_is_recorded_as_not_valid():
    r = {}
    _parse_grader_result(1, "SANY-STATUS: invalid\nFAIL [SANY-INVALID]\n", r)
    assert r["check_verdict"] == "FAIL"
    assert r["sany_status"] == "invalid"
    assert r["sany_valid"] is False


def test_sany_unavailable_is_an_error_without_changing_termination_reason():
    r = {"termination_reason": "OK"}
    _parse_grader_result(3, "SANY-STATUS: unavailable\nERROR\n", r)
    assert r["check_verdict"] == "ERROR"
    assert r["sany_status"] == "unavailable"
    assert r["sany_valid"] is False
    assert r["termination_reason"] == "OK"


def test_missing_sany_status_can_never_pass():
    r = {}
    _parse_grader_result(0, "PASS without a SANY marker\n", r)
    assert r["check_verdict"] == "ERROR"
    assert r["error"] == "grader did not report a SANY status"


if __name__ == "__main__":
    for _name, _fn in sorted(globals().items()):
        if _name.startswith("test_") and callable(_fn):
            _fn()
            print(f"ok  {_name}")
    print("all passed")
