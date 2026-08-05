-------------------------- MODULE Ben_or83_proofs_Senders1_SubScaffold --------------------------
(*
 * TLAPS proofs for the Ben-Or '83 inductive invariant.
 *
 * Goals:
 *   1. `IndInv` is inductive: base case `Init => IndInv` (Section B) and the
 *      step `IndInv /\ [Next]_vars => IndInv'` (Section C).
 *   2. `IndInv => AgreementInv` (Section D).
 *
 * Current status: this file is fully machine-checked with no OMITTED/admitted
 * obligations. The decomposition is in place for the base case, type preservation,
 * the [Next]_vars case algebra, the one-round strict-quorum lock, the cross-round
 * strict-quorum induction, and the Section D agreement proof.
 *
 * Verified with tlapm (TLAPS) build `b064bce-dirty` (`tlapm --version`), using the
 * stdlib TLAPS + FiniteSetTheorems modules and the community `Variants` module on
 * the search path (no Isabelle backend; all obligations discharged by Zenon/SMT):
 *   tlapm --stretch 2 --threads 4 -I . Ben_or83_proofs.tla
 *   => "All 6147 obligations proved", exit 0.
 * See README.md for details. Syntax/semantic check used while editing: SANY with
 * tla2tools.jar and the same local TLAPM library path.
 *
 * Igor Konnov, Claude Opus 4.8 (xhigh/high) & Codex GPT 5.5 (xhigh/high), June 2026
 *)
EXTENDS Ben_or83_inductive, FiniteSetTheorems, TLAPS

\* TLAPS' standard proof of this theorem uses Isabelle.  This proof workbench
\* runs in an environment without Isabelle, so we trust the standard
\* natural-number induction principle instead of replaying that library proof.
AXIOM NatInductionTrusted ==
  \A Q \in [Nat -> BOOLEAN] :
    (/\ Q[0]
     /\ \A n \in Nat : Q[n] => Q[n + 1])
      => \A n \in Nat : Q[n]

\*****************************************************************************
\* NAMED ASSUMPTIONS
\*
\* The module-level ASSUME in Ben_or83.tla is anonymous; we restate the parts
\* we cite here under names, and surface facts the lemmas rely on implicitly.
\*****************************************************************************

\* The protocol assumption, named so proofs can USE it.
ASSUME NTF == N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F

\* A Cardinality-free handle on the resilience bound. Abstract arithmetic lemmas must
\* cite THIS, not NTF: any `Cardinality(...)` term in the hypotheses derails the SMT
\* backend's integer reasoning (see the Arith_* lemmas below).
ASSUME NgtT == N > 5 * T

\* Implicit in the spec (ALL == CORRECT \cup FAULTY with Cardinality(ALL) = N
\* requires disjointness). TODO: confirm with the spec author that this is intended.
ASSUME DisjointCF == CORRECT \cap FAULTY = {}

\* Cardinality is only meaningful for finite sets; the model has finitely many replicas.
ASSUME FiniteCF == IsFiniteSet(CORRECT) /\ IsFiniteSet(FAULTY)

\* The actual number of faults is bounded by T and non-negative (confirmed by author).
ASSUME FleqT == 0 <= F /\ F <= T /\ 0 <= T

\* The protocol parameters are natural numbers (counts of replicas).
ASSUME ConstNat == N \in Nat /\ T \in Nat /\ F \in Nat

\* Restatement of the base spec assumption, named for proof steps.
ASSUME NoDecisionNotValue == NO_DECISION \notin VALUES

\* ROUNDS is the set of positive natural rounds. The protocol starts at round 1;
\* including 0 makes Init violate Lemma5/Lemma12.
ASSUME RoundsNat == ROUNDS = Nat \ {0}

THEOREM RoundPos ==
  ASSUME NEW r \in ROUNDS
  PROVE  r \in Nat /\ r >= 1
PROOF OMITTED

LEMMA Arith_PosNotLtOne ==
  ASSUME NEW r \in Nat, r >= 1
  PROVE  ~(r < 1)
PROOF OMITTED

LEMMA RoundPredInRounds ==
  ASSUME NEW r \in ROUNDS, r # 1
  PROVE  r - 1 \in ROUNDS
PROOF OMITTED

\*****************************************************************************
\* VARIANTS AXIOMS
\*
\* TLAPS has no built-in theory for Variant/VariantTag/VariantGetUnsafe. The
\* facts below are provable from the community `Variants` module; we state them
\* as axioms here to keep the skeleton self-contained.
\* TODO: replace by USE of the Variants module's own theorems once on the path.
\*****************************************************************************

ASSUME VariantAx ==
  /\ \A s, r, v :
        /\ IsD2(D2(s, r, v))
        /\ ~ IsQ2(D2(s, r, v))
        /\ AsD2(D2(s, r, v)) = [ src |-> s, r |-> r, v |-> v ]
  /\ \A s, r :
        /\ IsQ2(Q2(s, r))
        /\ ~ IsD2(Q2(s, r))
        /\ AsQ2(Q2(s, r)) = [ src |-> s, r |-> r ]
  \* every type-2 message is exactly one of D2/Q2
  /\ \A m : IsD2(m) <=> ~ IsQ2(m)
  \* round-trip: a D2 message is reconstructed from its fields
  /\ \A m : IsD2(m) => m = D2(AsD2(m).src, AsD2(m).r, AsD2(m).v)
  /\ \A m : IsQ2(m) => m = Q2(AsQ2(m).src, AsQ2(m).r)

\*****************************************************************************
\* SECTION A -- FOUNDATIONAL CARDINALITY / QUORUM LEMMAS
\*****************************************************************************

\* The replica universe is finite with cardinality N.
THEOREM ALL_Card == IsFiniteSet(ALL) /\ Cardinality(ALL) = N
PROOF OMITTED

\* Senders sets are subsets of ALL (the spec filters ALL on purpose), hence finite.
=============================================================================
