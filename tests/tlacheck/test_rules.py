"""Unit tests for the SANY-based cheat rules, on minimal synthetic modules.

Run: PYTHONPATH=src python3 -m pytest tests/tlacheck/test_rules.py
(or just: PYTHONPATH=src python3 tests/tlacheck/test_rules.py)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from tlacore.sany.dump import dump
from tlacore.provenance import Provenance
from tlacheck.context import CheckContext
from tlacheck.rules import admitted_statement, smuggled_module
from tlacheck.issue import Severity

FIX = os.path.join(os.path.dirname(__file__), "fixtures")


def _ctx(name, baseline=None):
    m = dump(os.path.join(FIX, name + ".tla"))
    return CheckContext(target_name=name, solution_dir=FIX, solution=m,
                        baseline=baseline, provenance=Provenance(target=name))


def _agent_ctx(agent_name):
    """Context where `agent_name` is an agent-CREATED module (provenance + parse)."""
    path = os.path.join(FIX, agent_name + ".tla")
    prov = Provenance(target="Target")
    prov.agent_created[agent_name] = path
    return CheckContext(target_name="Target", solution_dir=FIX, solution=None,
                        baseline=None, provenance=prov,
                        agent_modules={agent_name: dump(path)})


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


if __name__ == "__main__":
    test_clean_proof_not_flagged()
    test_bare_theorem_flagged()
    test_smuggled_obvious_module_flagged()
    test_proven_helper_module_not_flagged()
    print("ok: all tlacheck rule tests passed")
