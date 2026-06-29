"""Cheat-checker framework — the single sound-reduction predicate, as three gates.

This module IS the framework (W0): a benchmark solution passes iff

    PASS  ⟺  A (identity) ∧ B (discharge) ∧ C (trust)

  A — IDENTITY:  the thing that got proved IS the canonical target. The target
                 statement / CONSTANT / VARIABLE / ASSUME and the definitions it
                 depends on are unchanged (proof-completion preamble byte-identical); no new
                 AXIOM/ASSUME; no smuggled module or definition; the file parses
                 under standalone SANY.
  B — DISCHARGE: the target goal is genuinely discharged. tlapm proved every
                 generated obligation, no step is MISSING (bare QED / unproven
                 helper / unfinished target), the goal is not admitted as a
                 restated lemma, the agent added no PROOF OMITTED step, and (W3)
                 the only admitted steps are exactly the baseline's GIVEN lemmas.
  C — TRUST:     grading ran on trusted files — a given dependency was not
                 modified, and (W5) grading replays on canonical read-only
                 deps/model with tlapm unmodified.

"Cheating" is NOT a separate verdict: a cheat is simply some gate failing, so the
outcome is BINARY PASS/FAIL. The per-check reasons are kept for the agent's
in-run formative feedback — never as a CHEAT accusation. (See the project
discussion: a sound reduction lets feedback be transparent because there is no
exploitable gap left to game.) The A/B/C grouping organizes the checks for
humans; the agent sees the concrete check, not the abstract gate label.

This layer ORGANIZES existing detection onto the three gates (W1) and collapses
to a binary verdict (W2). It is the consolidation point for logic currently
spread across `tlacheck` rules, `tlapm --strict`, and the SANY validity check.

SAFETY INVARIANT (walking-skeleton migration): not-yet-built stronger checks are
PLACEHOLDERs that FAIL-OPEN. That is sound ONLY because the already-WIRED sibling
checks still cover every known cheat vector, so this layer is never LESS strict
than today's checker. Never delete a WIRED check before its stronger replacement
(the PARTIAL/PLACEHOLDER it would subsume) actually lands.

Roadmap (status per check below): W3 tighten admitted-set to a baseline set-diff;
W4 semantic statement-match (catch operator redefinition); W5 trusted-file replay
(discard dependency edits rather than merely detecting them).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum


class Gate(StrEnum):
    A_IDENTITY = "A:identity"  # proved thing IS the canonical target
    B_DISCHARGE = "B:discharge"  # target goal genuinely discharged
    C_TRUST = "C:trust"  # graded on trusted files


class Status(StrEnum):
    WIRED = "wired"  # real check, migrated from existing detection
    PARTIAL = "partial"  # works now; to be tightened (see TODO in detail)
    PLACEHOLDER = "placeholder"  # not implemented; FAIL-OPEN, covered by siblings


@dataclass
class Check:
    name: str
    gate: Gate
    status: Status
    ok: bool
    detail: str = ""


@dataclass
class GraderInputs:
    """What the existing detectors found, normalized into gate inputs.

    Computed by the caller (check_proof.py / the runner) from a tlacheck
    ``Result`` + the ``tlapm --strict`` status + SANY validity; see
    :func:`from_tlacheck`. Defaults are the "clean" values so a partially-filled
    instance never spuriously fails.
    """

    # Gate A — identity
    sany_valid: bool = True  # solution parses under standalone tla2sany
    statement_modified: bool = False  # target statement changed / weakened
    extra_axiom: bool = False  # new AXIOM/ASSUME beyond baseline
    smuggled_module: bool = False  # agent-created module sneaking content in
    preamble_modified: bool = False  # proof-completion preamble (defs/CONSTANT/VARIABLE/ASSUME) changed
    # Gate B — discharge
    tlapm_obligations_proved: bool = False  # every generated obligation PROVED, none failed
    n_missing: int = 0  # `--strict` MISSING steps (agent gaps)
    admitted_goal: bool = False  # a helper restates the target and is admitted
    proof_omitted: bool = False  # agent added a PROOF OMITTED / bare OMITTED step
    admitted_extra: bool = False  # agent added an admitted lemma beyond baseline (W3)
    # Gate C — trust
    deps_modified: bool = False  # a given dependency file was changed
    graded_on_canonical: bool = False  # grading used canonical read-only files (W5)


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

    def failed_integrity_checks(self) -> list[str]:
        """Names of failing INTEGRITY checks — a tamper/admit (the agent changed
        the statement, smuggled in an axiom/module, or admitted the goal), as
        opposed to an honest incomplete proof (a COMPLETION check) or a parse
        failure (sany_valid). Empty when the only failures are honest. The grade
        stays binary; this just labels *why* a FAIL happened for human reports."""
        return [c.name for c in self.checks if not c.ok and c.name in INTEGRITY_CHECKS]


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

# Checks whose failure means the agent TAMPERED/ADMITTED rather than honestly
# failed to finish. Used only to label a FAIL for human reports (the grade itself
# stays binary). NOT integrity: the COMPLETION checks ``obligations_proved`` /
# ``no_missing_steps`` (an honest unfinished proof) and the PARSE check
# ``sany_valid`` (an honest reject, surfaced separately). Note this is finer than
# the A/B/C gates — gate B mixes honest completion checks with admit-type cheats
# (``no_admitted_goal`` / ``no_added_omitted``), so cheat vs. honest can only be
# told apart at the check level, not the gate level.
INTEGRITY_CHECKS = frozenset(
    {
        "statement_unchanged",
        "no_extra_axiom",
        "no_smuggled_module",
        "no_smuggled_definition",
        "preamble_unchanged",
        "no_admitted_goal",
        "no_added_omitted",
        "admitted_set_eq_baseline",
        "deps_unmodified",
        "graded_on_canonical",
    }
)


def grade(inp: GraderInputs) -> GradeResult:
    """Evaluate the three gates and collapse to a binary verdict."""
    checks = [
        # ── Gate A: IDENTITY — the proved thing IS the canonical target ──────
        Check("sany_valid", Gate.A_IDENTITY, Status.WIRED, inp.sany_valid,
              "solution does not parse under standalone tla2sany"),
        Check("statement_unchanged", Gate.A_IDENTITY, Status.WIRED, not inp.statement_modified,
              "target theorem statement was changed or weakened"),
        Check("no_extra_axiom", Gate.A_IDENTITY, Status.WIRED, not inp.extra_axiom,
              "a new AXIOM/ASSUME was introduced beyond the baseline"),
        Check("no_smuggled_module", Gate.A_IDENTITY, Status.WIRED, not inp.smuggled_module,
              "an agent-created module smuggles content into the proof"),
        Check("preamble_unchanged", Gate.A_IDENTITY, Status.WIRED, not inp.preamble_modified,
              "the proof-completion preamble (definitions / CONSTANT / VARIABLE / ASSUME above PROOF OBVIOUS) was modified"),
        Check("no_smuggled_definition", Gate.A_IDENTITY, Status.PLACEHOLDER, True,
              "TODO(W4) semantic statement-match: catch redefining an operator used in the "
              "statement so the text is identical but the meaning is weaker"),
        # ── Gate B: DISCHARGE — the target goal is genuinely proved ──────────
        Check("obligations_proved", Gate.B_DISCHARGE, Status.WIRED, inp.tlapm_obligations_proved,
              "tlapm did not prove all generated obligations"),
        Check("no_missing_steps", Gate.B_DISCHARGE, Status.WIRED, inp.n_missing == 0,
              f"{inp.n_missing} step(s) have no proof (bare QED / unproven helper / unfinished target)"),
        Check("no_admitted_goal", Gate.B_DISCHARGE, Status.WIRED, not inp.admitted_goal,
              "the target goal is restated as an admitted (unproven) helper lemma"),
        Check("no_added_omitted", Gate.B_DISCHARGE, Status.WIRED, not inp.proof_omitted,
              "the agent added a PROOF OMITTED / bare OMITTED step (an unproven admit)"),
        Check("admitted_set_eq_baseline", Gate.B_DISCHARGE, Status.PARTIAL, not inp.admitted_extra,
              "TODO(W3) tighten to admitted-set == baseline; an admitted lemma was added"),
        # ── Gate C: TRUST — graded on trusted files ──────────────────────────
        Check("deps_unmodified", Gate.C_TRUST, Status.WIRED, not inp.deps_modified,
              "a given dependency file was modified"),
        Check("graded_on_canonical", Gate.C_TRUST, Status.PLACEHOLDER, True,
              "TODO(W5) trusted replay: re-run tlapm on canonical read-only deps + the agent's "
              "proof so dependency edits are discarded rather than merely detected"),
    ]
    return GradeResult(passed=all(c.ok for c in checks), checks=checks)


def from_tlacheck(result, *, tlapm_obligations_proved, n_missing, sany_valid,
                  preamble_modified=False, proof_omitted=False, graded_on_canonical=False):
    """Migrate existing detection onto the gate inputs (W1).

    Buckets a tlacheck ``Result``'s issues (by vector, ignoring WARNINGs) together
    with the ``tlapm --strict`` status and SANY validity into a
    :class:`GraderInputs`. ``result`` is duck-typed: any object exposing
    ``.issues`` where each issue has ``.vector`` and ``.severity`` (with a
    ``.value``/name distinguishing ``WARNING``).

    ``preamble_modified`` (proof-completion byte-match) and ``proof_omitted`` (agent-added
    PROOF OMITTED / bare OMITTED) are legacy-only detections that are not tlacheck
    vectors; the caller computes them. ``graded_on_canonical`` records whether the
    grade ran on trusted read-only files (W5).
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
        # admitted_extra (W3, the true baseline set-diff) is not computed yet; the
        # WIRED no_admitted_goal check covers the known cases until W3 lands.
        admitted_extra=False,
        deps_modified="DEPENDENCY_MODIFIED" in vectors,
        graded_on_canonical=graded_on_canonical,
    )
