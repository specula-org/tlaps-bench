"""Unit tests for the SANY-based cheat rules, on minimal synthetic modules.

Run: PYTHONPATH=src python3 -m pytest tests/tlacheck/test_rules.py
(or just: PYTHONPATH=src python3 tests/tlacheck/test_rules.py)
"""

from pathlib import Path

from tlacheck.context import CheckContext
from tlacheck.issue import Severity
from tlacheck.rules import admitted_statement, extra_axiom, smuggled_module, statement_modified
from tlacore.provenance import Provenance
from tlacore.sany.dump import dump

FIX = str(Path(__file__).parent / "fixtures")


def _fixture_path(name):
    return str(Path(FIX) / (name + ".tla"))


def _ctx(name, baseline=None):
    m = dump(_fixture_path(name))
    return CheckContext(
        target_name=name, solution_dir=FIX, solution=m, baseline=baseline, provenance=Provenance(target=name)
    )


def _agent_ctx(agent_name, solution_name=None):
    """Context where `agent_name` is an agent-CREATED module (provenance + parse).

    If `solution_name` is given, that fixture is the parsed solution (so the
    reachability filter can see whether the solution actually imports the agent
    module); otherwise solution is None.
    """
    path = _fixture_path(agent_name)
    prov = Provenance(target=solution_name or "Target")
    prov.agent_created[agent_name] = path
    solution = dump(_fixture_path(solution_name)) if solution_name else None
    return CheckContext(
        target_name=solution_name or "Target",
        solution_dir=FIX,
        solution=solution,
        baseline=None,
        provenance=prov,
        agent_modules={agent_name: dump(path)},
    )


def _axiom_ctx(solution_name, baseline_name):
    """Context with a parsed solution + baseline and their sources (for extra_axiom)."""
    sol_p = _fixture_path(solution_name)
    base_p = _fixture_path(baseline_name)
    return CheckContext(
        target_name=solution_name,
        solution_dir=FIX,
        solution=dump(sol_p),
        baseline=dump(base_p),
        provenance=Provenance(target=solution_name),
        solution_source=Path(sol_p).read_text(encoding="utf-8", errors="ignore"),
        baseline_source=Path(base_p).read_text(encoding="utf-8", errors="ignore"),
    )


def test_clean_proof_not_flagged():
    issues = admitted_statement.check(_ctx("CleanProof"))
    assert issues == [], f"clean proof wrongly flagged: {issues}"


def test_bare_theorem_flagged():
    issues = admitted_statement.check(_ctx("BareTheorem"))
    vectors = {i.vector for i in issues}
    assert "ADMITTED_STATEMENT" in vectors
    assert all(i.severity is Severity.CHEATING for i in issues)
    # Should flag both the bare 'Hard' and the circular 'Goal BY Hard'.
    msgs = " ".join(i.message for i in issues)
    assert "Hard" in msgs and "circular" in msgs


def test_smuggled_obvious_module_flagged():
    # An agent-created module exporting `THEOREM Goal == ... PROOF OBVIOUS` is a
    # smuggled axiom: tlapm trusts EXTENDS'd theorems and never re-checks them.
    issues = smuggled_module.check(_agent_ctx("SmuggledObvious"))
    assert any(i.vector == "SMUGGLED_MODULE" for i in issues), issues
    assert any("OBVIOUS" in i.message for i in issues)
    assert all(i.severity is Severity.CHEATING for i in issues)


def test_proven_helper_module_not_flagged():
    # A structured (non-OBVIOUS) proof in an agent module is legitimate
    # modularization, not a smuggled axiom.
    issues = smuggled_module.check(_agent_ctx("ProvenHelperModule"))
    assert issues == [], f"proven helper wrongly flagged: {issues}"


def test_unreferenced_scratch_module_not_flagged():
    # Regression: agents leave scratch modules (test2.tla) in the workspace that
    # the real solution never EXTENDS. tlapm never loads them, so a smuggled
    # axiom there is inert — must NOT be flagged.
    issues = smuggled_module.check(_agent_ctx("SmuggledObvious", solution_name="ScratchSolution"))
    assert issues == [], f"unreferenced scratch module wrongly flagged: {issues}"


def test_referenced_smuggled_module_flagged():
    # ...but when the solution DOES EXTEND the smuggled module, it is reachable
    # and the axiom is live — still caught.
    issues = smuggled_module.check(_agent_ctx("SmuggledObvious", solution_name="ImporterSolution"))
    assert any(i.vector == "SMUGGLED_MODULE" for i in issues), issues


def test_named_baseline_assume_not_flagged():
    # Regression: labelling the baseline's unnamed `ASSUME N \in Nat` as
    # `ASSUME NType == N \in Nat` so it can be cited BY name is not a new axiom.
    issues = extra_axiom.check(_axiom_ctx("NamedAssume", "BaselineAssume"))
    assert issues == [], f"named baseline assume wrongly flagged: {issues}"


def test_genuinely_new_axiom_flagged():
    # A new assumption absent from the baseline IS flagged.
    issues = extra_axiom.check(_axiom_ctx("NewAxiom", "BaselineAssume"))
    assert any(i.vector == "EXTRA_AXIOM" for i in issues), issues
    assert all(i.severity is Severity.CHEATING for i in issues)


def test_weakened_statement_flagged():
    # The agent weakened the target's claim (`\A n : n+0=n` -> `TRUE`). The
    # baseline statement no longer appears in the solution -> STATEMENT_MODIFIED.
    issues = statement_modified.check(_axiom_ctx("TargetWeak", "TargetStrong"))
    assert any(i.vector == "STATEMENT_MODIFIED" for i in issues), issues
    assert all(i.severity is Severity.CHEATING for i in issues)


def test_added_helper_lemma_not_flagged():
    # Proof-from-scratch FP guard: keeping the target statement verbatim while ADDING a
    # helper lemma above it is legitimate and must NOT trip the rule.
    issues = statement_modified.check(_axiom_ctx("TargetHelper", "TargetStrong"))
    assert issues == [], f"added helper lemma wrongly flagged: {issues}"


def test_statement_modified_no_baseline_source_is_noop():
    # Guard: without both sources the rule cannot slice statements -> returns [].
    ctx = _axiom_ctx("TargetWeak", "TargetStrong")
    ctx.baseline_source = None
    assert statement_modified.check(ctx) == []


if __name__ == "__main__":
    test_clean_proof_not_flagged()
    test_bare_theorem_flagged()
    test_smuggled_obvious_module_flagged()
    test_proven_helper_module_not_flagged()
    test_unreferenced_scratch_module_not_flagged()
    test_referenced_smuggled_module_flagged()
    test_named_baseline_assume_not_flagged()
    test_genuinely_new_axiom_flagged()
    test_weakened_statement_flagged()
    test_added_helper_lemma_not_flagged()
    test_statement_modified_no_baseline_source_is_noop()
    print("ok: all tlacheck rule tests passed")
