"""Cheat-checker framework — the single sound-reduction predicate, as three gates.

This module IS the framework: a benchmark solution passes iff

    PASS  ⟺  A (identity) ∧ B (discharge) ∧ C (trust)

  A — IDENTITY:  the thing that got proved IS the canonical target. The target
                 statement / CONSTANT / VARIABLE / ASSUME are unchanged (L1
                 preamble byte-identical); no new AXIOM/ASSUME; no smuggled
                 module; the file parses under standalone SANY.
  B — DISCHARGE: the target goal is genuinely discharged. tlapm proved every
                 generated obligation, no step is MISSING (bare QED / unproven
                 helper / unfinished target), the goal is not admitted as a
                 restated lemma, and the agent added no PROOF OMITTED step.
  C — TRUST:     grading ran on trusted files — a given dependency was not
                 modified (deps / model are read-only).

"Cheating" is NOT a separate verdict: a cheat is simply some gate failing, so the
outcome is BINARY PASS / FAIL. The per-check reasons (concrete check name +
explanation) are the agent's in-run formative feedback — never a CHEAT
accusation. The A/B/C grouping organizes the checks for humans; the agent sees
the concrete check, not the abstract gate label.

This is the consolidation point for logic spread across `tlacheck` rules,
`tlapm --strict`, and the SANY validity check.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum


class Gate(str, Enum):
    A_IDENTITY = "A:identity"  # proved thing IS the canonical target
    B_DISCHARGE = "B:discharge"  # target goal genuinely discharged
    C_TRUST = "C:trust"  # graded on trusted files


@dataclass
class Check:
    name: str
    gate: Gate
    ok: bool
    detail: str = ""


@dataclass
class GraderInputs:
    """What the existing detectors found, normalized into gate inputs.

    Computed by the caller (check_proof.py) from a tlacheck ``Result`` + the
    ``tlapm --strict`` status + SANY validity; see :func:`from_tlacheck`. Defaults
    are the "clean" values so a partially-filled instance never spuriously fails.
    """

    # Gate A — identity
    sany_valid: bool = True  # solution parses under standalone tla2sany
    statement_modified: bool = False  # target statement changed / weakened
    extra_axiom: bool = False  # new AXIOM/ASSUME beyond baseline
    smuggled_module: bool = False  # agent-created module sneaking content in
    preamble_modified: bool = False  # L1 preamble (defs/CONSTANT/VARIABLE/ASSUME) changed
    # Gate B — discharge
    tlapm_obligations_proved: bool = False  # every generated obligation PROVED, none failed
    n_missing: int = 0  # `--strict` MISSING steps (agent gaps)
    admitted_goal: bool = False  # a helper restates the target and is admitted
    proof_omitted: bool = False  # agent added a PROOF OMITTED / bare OMITTED step
    # Gate C — trust
    deps_modified: bool = False  # a given dependency file was changed


@dataclass
class GradeResult:
    passed: bool
    checks: list[Check] = field(default_factory=list)

    @property
    def reasons(self) -> list[str]:
        """Concrete failing-check reasons for agent feedback (no abstract gate prefix)."""
        return [f"{c.name}: {c.detail}" for c in self.checks if not c.ok]

    def failed_gates(self) -> list[Gate]:
        return sorted({c.gate for c in self.checks if not c.ok}, key=lambda g: g.value)


# Single migration map: which tlacheck issue vector belongs to which gate.
VECTOR_GATE = {
    "STATEMENT_MODIFIED": Gate.A_IDENTITY,
    "EXTRA_AXIOM": Gate.A_IDENTITY,
    "SMUGGLED_MODULE": Gate.A_IDENTITY,
    "ADMITTED_STATEMENT": Gate.B_DISCHARGE,
    "ADMITTED_FALLBACK": Gate.B_DISCHARGE,
    "INCOMPLETE_PROOF": Gate.B_DISCHARGE,
    "DEPENDENCY_MODIFIED": Gate.C_TRUST,
}


def grade(inp: GraderInputs) -> GradeResult:
    """Evaluate the three gates and collapse to a binary verdict."""
    checks = [
        # Gate A — identity: the proved thing IS the canonical target
        Check("sany_valid", Gate.A_IDENTITY, inp.sany_valid,
              "solution does not parse under standalone tla2sany"),
        Check("statement_unchanged", Gate.A_IDENTITY, not inp.statement_modified,
              "target theorem statement was changed or weakened"),
        Check("no_extra_axiom", Gate.A_IDENTITY, not inp.extra_axiom,
              "a new AXIOM/ASSUME was introduced beyond the baseline"),
        Check("no_smuggled_module", Gate.A_IDENTITY, not inp.smuggled_module,
              "an agent-created module smuggles content into the proof"),
        Check("preamble_unchanged", Gate.A_IDENTITY, not inp.preamble_modified,
              "the L1 preamble (definitions / CONSTANT / VARIABLE / ASSUME above PROOF OBVIOUS) was modified"),
        # Gate B — discharge: the target goal is genuinely proved
        Check("obligations_proved", Gate.B_DISCHARGE, inp.tlapm_obligations_proved,
              "tlapm did not prove all generated obligations"),
        Check("no_missing_steps", Gate.B_DISCHARGE, inp.n_missing == 0,
              f"{inp.n_missing} step(s) have no proof (bare QED / unproven helper / unfinished target)"),
        Check("no_admitted_goal", Gate.B_DISCHARGE, not inp.admitted_goal,
              "the target goal is restated as an admitted (unproven) helper lemma"),
        Check("no_added_omitted", Gate.B_DISCHARGE, not inp.proof_omitted,
              "the agent added a PROOF OMITTED / bare OMITTED step (an unproven admit)"),
        # Gate C — trust: graded on trusted files
        Check("deps_unmodified", Gate.C_TRUST, not inp.deps_modified,
              "a given dependency file was modified"),
    ]
    return GradeResult(passed=all(c.ok for c in checks), checks=checks)


def from_tlacheck(result, *, tlapm_obligations_proved, n_missing, sany_valid,
                  preamble_modified=False, proof_omitted=False):
    """Migrate existing detection onto the gate inputs.

    Buckets a tlacheck ``Result``'s issues (by vector, ignoring WARNINGs) together
    with the ``tlapm --strict`` status and SANY validity into a
    :class:`GraderInputs`. ``result`` is duck-typed: any object exposing
    ``.issues`` where each issue has ``.vector`` and ``.severity`` (with a
    ``.value`` distinguishing ``WARNING``).

    ``preamble_modified`` (L1 byte-match) and ``proof_omitted`` (agent-added
    PROOF OMITTED / bare OMITTED) are legacy-only detections that are not tlacheck
    vectors; the caller computes them.
    """
    vectors = {
        i.vector
        for i in getattr(result, "issues", [])
        if getattr(getattr(i, "severity", None), "value", None) != "WARNING"
    }
    return GraderInputs(
        sany_valid=sany_valid,
        statement_modified="STATEMENT_MODIFIED" in vectors,
        extra_axiom="EXTRA_AXIOM" in vectors,
        smuggled_module="SMUGGLED_MODULE" in vectors,
        preamble_modified=preamble_modified,
        tlapm_obligations_proved=tlapm_obligations_proved,
        n_missing=n_missing,
        admitted_goal=bool(vectors & {"ADMITTED_STATEMENT", "ADMITTED_FALLBACK"}),
        proof_omitted=proof_omitted,
        deps_modified="DEPENDENCY_MODIFIED" in vectors,
    )
