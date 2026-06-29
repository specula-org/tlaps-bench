"""Tests for the cheat-checker gate framework (src/tlacheck/gates.py).

Covers: the binary PASS/FAIL collapse, each WIRED gate check failing the run,
PLACEHOLDER checks failing-open (so the skeleton is never less strict than the
wired siblings but unbuilt checks don't block), the caller-computed legacy
signals (proof-completion preamble byte-match, agent-added PROOF OMITTED) flowing to their
gates, and the from_tlacheck migration mapping real tlacheck issue vectors onto
the right gate.

Run: PYTHONPATH=src python3 -m pytest tests/tlacheck/test_gates.py
(or:  PYTHONPATH=src python3 tests/tlacheck/test_gates.py)
"""

from tlacheck.gates import Gate, GraderInputs, Status, from_tlacheck, grade
from tlacheck.issue import Issue, Severity
from tlacheck.verdict import Result, Verdict

# A fully clean, genuinely-proved solution.
CLEAN = GraderInputs(
    sany_valid=True,
    statement_modified=False,
    extra_axiom=False,
    smuggled_module=False,
    preamble_modified=False,
    tlapm_obligations_proved=True,
    n_missing=0,
    admitted_goal=False,
    proof_omitted=False,
    admitted_extra=False,
    deps_modified=False,
    graded_on_canonical=True,
)


def test_clean_passes():
    r = grade(CLEAN)
    assert r.passed
    assert r.reasons == []


def test_each_wired_failure_fails_the_run():
    # (field to flip, expected failing gate, bad value)
    cases = [
        ("sany_valid", Gate.A_IDENTITY, False),
        ("statement_modified", Gate.A_IDENTITY, True),
        ("extra_axiom", Gate.A_IDENTITY, True),
        ("smuggled_module", Gate.A_IDENTITY, True),
        ("preamble_modified", Gate.A_IDENTITY, True),
        ("tlapm_obligations_proved", Gate.B_DISCHARGE, False),
        ("admitted_goal", Gate.B_DISCHARGE, True),
        ("proof_omitted", Gate.B_DISCHARGE, True),
        ("deps_modified", Gate.C_TRUST, True),
    ]
    for field_name, gate, bad_value in cases:
        inp = GraderInputs(**{**CLEAN.__dict__, field_name: bad_value})
        r = grade(inp)
        assert not r.passed, f"{field_name}={bad_value} should FAIL"
        assert gate in r.failed_gates(), f"{field_name} should fail gate {gate}"
        assert r.reasons, f"{field_name} failure should surface a reason"


def test_missing_step_fails_gate_b():
    r = grade(GraderInputs(**{**CLEAN.__dict__, "n_missing": 1}))
    assert not r.passed
    assert Gate.B_DISCHARGE in r.failed_gates()


def test_placeholders_fail_open():
    # On a clean input, the only PLACEHOLDER/PARTIAL checks must NOT block.
    r = grade(CLEAN)
    placeholders = [c for c in r.checks if c.status is Status.PLACEHOLDER]
    assert placeholders, "scaffold should carry explicit placeholders (W4/W5)"
    assert all(c.ok for c in placeholders), "placeholders must fail-open"
    assert r.passed


def test_binary_no_cheat_category():
    # A 'cheating' input (extra axiom) is just FAIL — there is no CHEAT verdict.
    r = grade(GraderInputs(**{**CLEAN.__dict__, "extra_axiom": True}))
    assert r.passed is False  # strictly binary


def _result(*vectors, severity=Severity.CHEATING):
    return Result(Verdict.CHEATING, [Issue(v, severity, f"test {v}") for v in vectors])


def test_from_tlacheck_buckets_vectors():
    # Each real tlacheck vector lands in the right gate and fails the run.
    expect = {
        "STATEMENT_MODIFIED": Gate.A_IDENTITY,
        "EXTRA_AXIOM": Gate.A_IDENTITY,
        "SMUGGLED_MODULE": Gate.A_IDENTITY,
        "ADMITTED_STATEMENT": Gate.B_DISCHARGE,
        "ADMITTED_FALLBACK": Gate.B_DISCHARGE,
        "DEPENDENCY_MODIFIED": Gate.C_TRUST,
    }
    for vector, gate in expect.items():
        inp = from_tlacheck(_result(vector), tlapm_obligations_proved=True, n_missing=0, sany_valid=True)
        r = grade(inp)
        assert not r.passed, f"{vector} should FAIL the run"
        assert gate in r.failed_gates(), f"{vector} should map to {gate}"


def test_from_tlacheck_legacy_signals_flow_to_gates():
    # proof-completion preamble byte-match (gate A) and agent-added PROOF OMITTED (gate B) are
    # not tlacheck vectors — they come in as explicit caller-computed flags.
    pre = from_tlacheck(
        _result(), tlapm_obligations_proved=True, n_missing=0, sany_valid=True, preamble_modified=True
    )
    assert not grade(pre).passed
    assert Gate.A_IDENTITY in grade(pre).failed_gates()
    omit = from_tlacheck(
        _result(), tlapm_obligations_proved=True, n_missing=0, sany_valid=True, proof_omitted=True
    )
    assert not grade(omit).passed
    assert Gate.B_DISCHARGE in grade(omit).failed_gates()


def test_from_tlacheck_clean_result_passes():
    inp = from_tlacheck(
        _result(), tlapm_obligations_proved=True, n_missing=0, sany_valid=True, graded_on_canonical=True
    )
    assert grade(inp).passed


def test_from_tlacheck_ignores_warnings():
    # A WARNING-severity issue must not fail any gate.
    inp = from_tlacheck(
        _result("DEPENDENCY_MODIFIED", severity=Severity.WARNING),
        tlapm_obligations_proved=True,
        n_missing=0,
        sany_valid=True,
    )
    assert grade(inp).passed


def test_from_tlacheck_strict_status_flows_to_gate_b():
    # tlapm not proving / a missing step comes from the strict status, not issues.
    not_proved = from_tlacheck(_result(), tlapm_obligations_proved=False, n_missing=0, sany_valid=True)
    assert not grade(not_proved).passed
    missing = from_tlacheck(_result(), tlapm_obligations_proved=True, n_missing=2, sany_valid=True)
    assert not grade(missing).passed
    assert Gate.B_DISCHARGE in grade(missing).failed_gates()


def test_failed_integrity_checks_separate_cheats_from_honest_fails():
    # A tamper/admit fails an INTEGRITY check (a cheat); an unfinished proof or a
    # parse failure does not — even when they share an A/B/C gate.
    cheat = grade(GraderInputs(**{**CLEAN.__dict__, "extra_axiom": True}))
    assert cheat.failed_integrity_checks() == ["no_extra_axiom"]
    # admitted_goal lives under gate B (with the honest completion checks) but IS
    # a cheat — the reason check-level, not gate-level, is the right granularity.
    admit = grade(GraderInputs(**{**CLEAN.__dict__, "admitted_goal": True}))
    assert admit.failed_integrity_checks() == ["no_admitted_goal"]
    # Honest incomplete proof: no integrity check fails.
    assert grade(GraderInputs(**{**CLEAN.__dict__, "tlapm_obligations_proved": False})).failed_integrity_checks() == []
    assert grade(GraderInputs(**{**CLEAN.__dict__, "n_missing": 1})).failed_integrity_checks() == []
    # Parse failure is an honest reject, not a cheat.
    assert grade(GraderInputs(**{**CLEAN.__dict__, "sany_valid": False})).failed_integrity_checks() == []


if __name__ == "__main__":
    for _name, _fn in sorted(globals().items()):
        if _name.startswith("test_") and callable(_fn):
            _fn()
            print(f"ok  {_name}")
    print("all passed")
