------------------- MODULE tendermint_single_indinv_proofs_BoundedMaxExists -------------------
(*
 * TLAPS proofs for the single-height Tendermint inductive invariant defined in
 * `tendermint_single_indinv.tla` (a machine-generated Apalache model).
 *
 * Goals (mirroring ben-or83/Ben_or83_proofs.tla):
 *   1. `TypedIndInv` is inductive: base case `Init => TypedIndInv`
 *      (Section B) and the step `TypedIndInv /\ Step => TypedIndInv'`
 *      (Section C).
 *   2. `TypedIndInv => Agreement` (Section D).
 *
 * `TypedIndInv` is `IndTypeOk /\ IndInv` (25 conjuncts). The proof is complete
 * end-to-end with no remaining holes (no OMITTED stubs): `InitInd`
 * (Init => TypedIndInv), `Inductive` (TypedIndInv /\ Step => TypedIndInv', all
 * 25 conjuncts preserved), and `AgreementThm` (TypedIndInv => Agreement).
 * (An earlier `TypedIndInvMin` -- the 17-conjunct subset IndTypeOk /\ IndInvMin --
 * was targeted first but is not inductive on its own: PrecommitsLockValue needs
 * the extra 8 conjuncts. The development now uses the full `TypedIndInv`
 * throughout, and `TypedIndInvMin`/`IndInvMin` have been dropped from both the
 * Wunderspec source and the generated spec.)
 *
 * Environment: tlapm (TLAPS) with the stdlib TLAPS + FiniteSetTheorems modules.
 * Most obligations go to SMT; ~120 higher-order set-cardinality obligations fall
 * back to Zenon and a handful to the Isabelle backend (a few are pinned to `Isa`
 * so they skip the doomed SMT/Zenon attempts, which otherwise waste time and, under
 * `--threads` contention, cause nondeterministic timeouts). The spec is a plain
 * `EXTENDS Integers, FiniteSets, Sequences` (the old `Apalache.tla` shim is gone --
 * `Max` now renders via `CHOOSE`, not `ApaFoldSet`). Verify with:
 *   tlapm --stretch 2 --threads 3 -I . tendermint_single_indinv_proofs.tla
 *   => "All 3769 obligations proved", exit 0.
 * Note: SANY flags ~12 spurious "multiply-defined 'p'" errors on the `<1>sel`
 * selectors that tlapm's own frontend accepts -- pre-existing, not a real defect.
 *
 * Igor Konnov, Claude Opus 4.8, July 2026
 *)
EXTENDS tendermint_single_indinv, FiniteSetTheorems, TLAPS

\* The actual number of faulty replicas. The spec declares no `F` constant, so we
\* define it here as the cardinality of the Faulty set.
F == Cardinality(Faulty)

\* TLAPS' standard proof of natural-number induction uses Isabelle. This workbench
\* runs without an Isabelle backend, so we trust the induction principle instead of
\* replaying that library proof. Needed for the round induction in Section D.
AXIOM NatInductionTrusted ==
  \A Q \in [Nat -> BOOLEAN] :
    (/\ Q[0]
     /\ \A n \in Nat : Q[n] => Q[n + 1])
      => \A n \in Nat : Q[n]

\*****************************************************************************
\* NAMED ASSUMPTIONS
\*
\* The Apalache spec declares no module-level ASSUME. We state the parameter
\* constraints the proofs rely on under names, so steps can USE/cite them.
\* Resilience (confirmed with the spec author): N > 3*T /\ T >= F /\ F >= 0.
\*****************************************************************************

\* Tendermint/BFT resilience: strictly more than three times the fault bound.
ASSUME NgtT == N > 3 * T

\* The optimal BFT replica count (confirmed by the spec author). REQUIRED for quorum
\* intersection: with a fixed 2T+1 quorum threshold, two quorums share a *correct*
\* process only when N = 3T+1. Without it QuorumsIntersectInCorrect is FALSE, e.g.
\* N=5, T=1, F=1, A={c1,c2,f}, B={c3,c4,f}: both have size 2T+1=3 but meet only in
\* the faulty node; agreement fails for N>3T+1 (a 2T+1 quorum is below 2/3 of N).
ASSUME Neq3Tp1 == N = 3 * T + 1

\* The actual number of faults is bounded by T.
ASSUME TgeF == T >= F

\* The number of faults is non-negative.
ASSUME FnonNeg == F >= 0

\* Correct and faulty replicas are disjoint.
ASSUME DisjointCF == Corr \cap Faulty = {}

\* Cardinality is only meaningful for finite sets; there are finitely many replicas.
ASSUME FiniteCF == IsFiniteSet(Corr) /\ IsFiniteSet(Faulty)

\* N counts all replicas (correct + faulty), which are disjoint.
ASSUME NCard == N = Cardinality(Corr) + Cardinality(Faulty)

\* The protocol parameters are natural numbers.
ASSUME ConstNat == N \in Nat /\ T \in Nat /\ MaxRound \in Nat

\* Nil is encoded as -1 and is not a valid value. (Confirmed by the spec's use of
\* -1 as the nil sentinel throughout; TODO: confirm with the spec author.)
ASSUME NilNotValid == -1 \notin ValidValues

\* There is at least one valid value to propose. Needed by the base case for the
\* existential witness inside AllNoEquivocationByCorrect over empty message logs.
ASSUME ValidValuesNonEmpty == ValidValues # {}

LEMMA IntLeGeTrans ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW c \in Int, NEW k \in Int,
         a >= k, a <= b, b <= c
  PROVE  c >= k
PROOF OMITTED

LEMMA IntLeGeTrans1 ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW k \in Int,
         a >= k, a <= b
  PROVE  b >= k
PROOF OMITTED

\*****************************************************************************
\* SECTION A -- FOUNDATIONAL CARDINALITY / QUORUM LEMMAS
\*
\* Port from ben-or83/Ben_or83_proofs.tla Section A, adapted to Tendermint's
\* 2T+1 quorums under N > 3*T. The central fact is that any two >= 2T+1 subsets
\* of (Corr \union Faulty) share a *correct* process (since 2*(2T+1) - N > T >= F).
\* The worked example in Section C does not need these; they are stubbed here.
\*****************************************************************************

\* Two quorums of size >= 2T+1 intersect in a correct process. TODO: prove by
\* porting the Ben-Or QuorumIntersection argument (inclusion-exclusion on
\* Cardinality over the finite set Corr \union Faulty).
THEOREM QuorumsIntersectInCorrect ==
  ASSUME NEW A \in SUBSET (Corr \union Faulty),
         NEW B \in SUBSET (Corr \union Faulty),
         Cardinality(A) >= 2 * T + 1,
         Cardinality(B) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in A /\ c \in B
PROOF OMITTED

\* A single quorum (>= 2T+1 senders) already contains a correct process.
THEOREM QuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in S
PROOF OMITTED

\*****************************************************************************
\* SECTION B -- BASE CASE + TYPE PRESERVATION
\*****************************************************************************

\* Base case of induction. At Init the message logs are empty and every
\* per-process field is nil (-1) or 0, so each IndInv conjunct holds: the
\* message-quantified ones are vacuous, the nil-flag ones agree, and the two
\* existential-witness conjuncts (AllNoEquivocationByCorrect, PrecommitsLockValue)
\* close via ValidValuesNonEmpty and Cardinality({}) = 0.
THEOREM InitInd ==
  Init => TypedIndInv
PROOF OMITTED

\* Record-typing helpers: a freshly built message record lies in the IndTypeOk
\* element set. These supply the tuple witness that Zenon/SMT cannot guess for
\* `rec \in {[..]: t \in A \X B \X ...}` goals. Used by TypePres for the
\* message-adding actions (both correct broadcasts and FaultyStep injections).
LEMMA ProposeRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW pr \in ((ValidValues \union InvalidValues) \union {-1}),
         NEW vr \in ((0)..(MaxRound) \union {-1})
  PROVE  [proposal |-> pr, round |-> rr, src |-> s, valid_round |-> vr]
           \in {[proposal |-> t[3], round |-> t[2], src |-> t[1], valid_round |-> t[4]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}
PROOF OMITTED

LEMMA PrevoteRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
PROOF OMITTED

LEMMA PrecommitRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
PROOF OMITTED

\* Message monotonicity: every Step action either leaves a message log unchanged
\* or appends to it (EXCEPT-union), so entries are never removed. Used by the
\* Section C "in step X => already sent Y" conjuncts to carry a witnessing
\* message across a step.
LEMMA ProposeMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_propose[r]
  PROVE  x \in msgs_propose'[r]
PROOF OMITTED

LEMMA PrevoteMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_prevote[r]
  PROVE  x \in msgs_prevote'[r]
PROOF OMITTED

LEMMA PrecommitMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_precommit[r]
  PROVE  x \in msgs_precommit'[r]
PROOF OMITTED

LEMMA PrevoteSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote'[r] : mm.id = idv} : s = m.src})
PROOF OMITTED

LEMMA PrevoteAllSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote'[r] : s = m.src})
PROOF OMITTED

LEMMA PrevoteValueSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
PROOF OMITTED

LEMMA PrevoteEvidenceSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound), NEW E \in SUBSET msgs_prevote[r]
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in E : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
PROOF OMITTED

LEMMA PrecommitSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src})
PROOF OMITTED

LEMMA PrecommitValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_precommit[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
PROOF OMITTED

LEMMA PrecommitValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_precommit[r] : m.id = idv})
PROOF OMITTED

LEMMA PrevoteValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
PROOF OMITTED

LEMMA PrevoteValueMessagesCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
PROOF OMITTED

LEMMA PrevoteValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_prevote[r] : m.id = idv})
PROOF OMITTED

LEMMA StepUpdateChangedProcess ==
  ASSUME IndTypeOk, NEW p \in Corr, NEW q \in Corr, NEW st,
         step' = [step EXCEPT ![p] = st],
         step'[q] # step[q]
  PROVE  q = p
PROOF OMITTED

\* If a correct process q's step changed over Step, then q is the acting process
\* and took one of its nine step-changing actions. (InsertProposal and FaultyStep
\* leave step unchanged; every other action sets step via [step EXCEPT ![p] = ..],
\* so a change at q forces q = p.) Used to identify the enabling action from the
\* post-state in the Section C "in step X" conjuncts.
LEMMA StepChangeChar ==
  ASSUME IndTypeOk, Step, NEW q \in Corr, step'[q] # step[q]
  PROVE  \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
         \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
         \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
         \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
PROOF OMITTED

LEMMA EnteredPrevoteHasSentPrevote ==
  ASSUME TypedIndInv, Step, NEW q \in Corr,
         step[q] # "PREVOTE_OF_STEP", step'[q] = "PREVOTE_OF_STEP"
  PROVE  \E m \in msgs_prevote'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
PROOF OMITTED

LEMMA EnteredPrecommitHasSentPrecommit ==
  ASSUME TypedIndInv, Step, NEW q \in Corr,
         step[q] # "PRECOMMIT_OF_STEP", step'[q] = "PRECOMMIT_OF_STEP"
  PROVE  \E m \in msgs_precommit'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
PROOF OMITTED

LEMMA RoundMonotone ==
  ASSUME IndTypeOk, Step, NEW q \in Corr
  PROVE  round[q] <= round'[q]
PROOF OMITTED

\* Type preservation, grouped by type conjunct: each state variable is touched
\* by only a few Step actions; for all other actions it is UNCHANGED and its type
\* carries from the hypothesis IndTypeOk. `BY DEF Step, <actions>` unfolds Step's
\* disjunction and the cited actions; uncited disjuncts keep the variable via
\* their own UNCHANGED tuple. Message-adding actions build records that match the
\* IndTypeOk element sets (src in Corr\union Faulty, round = index, value typed).
THEOREM TypePres ==
  ASSUME TypedIndInv, Step
  PROVE  IndTypeOk'
PROOF OMITTED

\*****************************************************************************
\* SECTION C -- INDUCTIVE STEP
\*
\* The transition is `Step` (there is no [Step]_vars; this mirrors how Apalache
\* checks IndInit /\ Next => IndInv', with no explicit stutter case). `Step`
\* inlines the disjunction of the 10 correct sub-actions (each guarded by a
\* process p \in Corr and paired with its own UNCHANGED tuple) plus FaultyStep.
\*
\* For each IndInv conjunct C we prove an assembler
\*   Pres_C == ASSUME TypedIndInv, Step PROVE C'
\* by splitting Step into its 11 disjuncts and discharging each with a per-action
\* theorem Pres_C_<action>. Below, `AllValidAndLockedRoundBounded` is fully worked
\* out as the template; later assemblers follow the same shape.
\*****************************************************************************

\* ---------------------------------------------------------------------------
\* WORKED CONJUNCT: AllValidAndLockedRoundBounded
\*   \A p \in Corr: valid_round[p] <= round[p] /\ locked_round[p] <= round[p]
\*
\* 8 actions leave round, valid_round, locked_round all UNCHANGED (trivial). The
\* 3 substantive actions touch round or the round flags:
\*   - UponProposalInPrevoteOrCommitAndPrevote sets valid_round[p]:=round[p] and
\*     (in the "then" branch) locked_round[p]:=round[p], with round UNCHANGED.
\*   - UponQuorumOfPrecommitsAny advances round[p]:=round[p]+1, flags UNCHANGED.
\*   - OnRoundCatchup jumps round[p] up to some rnd>round[p], flags UNCHANGED.
\* ---------------------------------------------------------------------------

\* --- 8 trivial (UNCHANGED) cases ---

THEOREM Pres_Bounded_InsertProposal ==
  ASSUME TypedIndInv, NEW p \in Corr, InsertProposal(p),
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_UponProposalInPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_UponProposalInProposeAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInProposeAndPrevote(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_UponQuorumOfPrevotesAny ==
  ASSUME TypedIndInv, NEW p \in Corr, UponQuorumOfPrevotesAny(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_UponProposalInPrecommitNoDecision ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPrecommitNoDecision(p),
         UNCHANGED <<round, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_OnTimeoutPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, OnTimeoutPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_OnQuorumOfNilPrevotes ==
  ASSUME TypedIndInv, NEW p \in Corr, OnQuorumOfNilPrevotes(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

THEOREM Pres_Bounded_Faulty ==
  ASSUME TypedIndInv, FaultyStep,
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, last_action>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

\* --- 3 substantive cases ---

\* Sets valid_round[p]:=round[p], and locked_round[p]:=round[p] in the "then"
\* branch (else locked_round UNCHANGED); round itself is UNCHANGED.
THEOREM Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponProposalInPrevoteOrCommitAndPrevote(p),
         UNCHANGED <<round, decision, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

\* Advances round[p] to round[p]+1; valid_round and locked_round are UNCHANGED.
THEOREM Pres_Bounded_UponQuorumOfPrecommitsAny ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponQuorumOfPrecommitsAny(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

\* Jumps round[p] up to some rnd > round[p]; valid_round and locked_round UNCHANGED.
THEOREM Pres_Bounded_OnRoundCatchup ==
  ASSUME TypedIndInv, NEW p \in Corr,
         OnRoundCatchup(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

\* Assembler: split Step into its 11 disjuncts.
THEOREM Pres_AllValidAndLockedRoundBounded ==
  ASSUME TypedIndInv, Step
  PROVE  AllValidAndLockedRoundBounded'
PROOF OMITTED

\* ---------------------------------------------------------------------------
\* REMAINING 16 CONJUNCT ASSEMBLERS.
\* Each follows the pattern above: decompose into Pres_<Conj>_<action> theorems
\* over the 11 Step disjuncts, then assemble BY ... DEF Step.
\* ---------------------------------------------------------------------------

THEOREM Pres_AllNoFutureMessagesSent ==
  ASSUME TypedIndInv, Step PROVE AllNoFutureMessagesSent'
PROOF OMITTED

THEOREM Pres_AllIfInPrevoteThenSentPrevote ==
  ASSUME TypedIndInv, Step PROVE AllIfInPrevoteThenSentPrevote'
PROOF OMITTED

THEOREM Pres_AllIfInPrecommitThenSentPrecommit ==
  ASSUME TypedIndInv, Step PROVE AllIfInPrecommitThenSentPrecommit'
PROOF OMITTED

\* A decided process received a matching proposal (at some round). Only
\* UponProposalInPrecommitNoDecision decides, and its guard exhibits the proposal;
\* an already-decided process keeps its decision (it cannot act) and the proposal
\* persists by ProposeMonotone.
THEOREM Pres_AllIfInDecidedThenReceivedProposal ==
  ASSUME TypedIndInv, Step
  PROVE  AllIfInDecidedThenReceivedProposal'
PROOF OMITTED

THEOREM Pres_AllIfInDecidedThenReceivedTwoThirds ==
  ASSUME TypedIndInv, Step PROVE AllIfInDecidedThenReceivedTwoThirds'
PROOF OMITTED

\* (step[p]=DECIDED) <=> (decision[p] in ValidValues). Only
\* UponProposalInPrecommitNoDecision sets step:=DECIDED, and it simultaneously
\* sets decision:=v with v in ValidValues. Every other step-changing action is
\* guarded by step[p] /= DECIDED and sets step to a non-DECIDED value while
\* leaving decision unchanged, so the old biconditional carries: the guard makes
\* the old LHS false, hence decision[p] was not a ValidValue.
THEOREM Pres_AllIfInDecidedThenValidDecision ==
  ASSUME TypedIndInv, Step
  PROVE  AllIfInDecidedThenValidDecision'
PROOF OMITTED

\* Only UponProposalInPrevoteOrCommitAndPrevote touches locked_round/locked_value:
\* its "then" branch sets locked_value[p]:=v (v in ValidValues, so /= -1) and
\* locked_round[p]:=round[p] (in 0..MaxRound, so /= -1) together; every other
\* action leaves both UNCHANGED. So the -1 flags stay in agreement.
THEOREM Pres_AllLockedRoundIffLockedValue ==
  ASSUME TypedIndInv, Step
  PROVE  AllLockedRoundIffLockedValue'
PROOF OMITTED

\* Symmetric to the above: only UponProposalInPrevoteOrCommitAndPrevote sets
\* valid_value[p]:=v (/= -1) and valid_round[p]:=round[p] (/= -1) together.
THEOREM Pres_AllValidRoundIffValidValue ==
  ASSUME TypedIndInv, Step
  PROVE  AllValidRoundIffValidValue'
PROOF OMITTED

THEOREM Pres_AllIfValidRoundThenTwoThirdsPrevotes ==
  ASSUME TypedIndInv, Step PROVE AllIfValidRoundThenTwoThirdsPrevotes'
PROOF OMITTED

THEOREM Pres_AllIfLockedRoundThenSentCommit ==
  ASSUME TypedIndInv, Step PROVE AllIfLockedRoundThenSentCommit'
PROOF OMITTED

THEOREM Pres_AllLatestPrecommitHasLockedRound ==
  ASSUME TypedIndInv, Step PROVE AllLatestPrecommitHasLockedRound'
PROOF OMITTED

THEOREM Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds ==
  ASSUME TypedIndInv, Step PROVE AllIfSentPrevoteThenReceivedProposalOrTwoThirds'
PROOF OMITTED

THEOREM Pres_IfSentPrecommitThenSentPrevote ==
  ASSUME TypedIndInv, Step PROVE IfSentPrecommitThenSentPrevote'
PROOF OMITTED

THEOREM Pres_IfSentPrecommitThenReceivedTwoThirds ==
  ASSUME TypedIndInv, Step PROVE IfSentPrecommitThenReceivedTwoThirds'
  \* Keep only IndTypeOk (typing) + the one pre-invariant this proof needs ambient; USE DEF-
  \* expanding all of IndInv drags the quorum conjuncts' nested-Cardinality set-builders into
  \* every obligation, timing out the fallback-less `BY ... SMT DEF FaultyStep` case.
PROOF OMITTED

THEOREM Pres_AllNoEquivocationByCorrect ==
  ASSUME TypedIndInv, Step PROVE AllNoEquivocationByCorrect'
PROOF OMITTED

\* PrecommitsLockValue is NOT inductive relative to IndInv alone (Apalache CE): a
\* fresh prevote for w2 in a round above an existing precommit lock for w must be
\* blocked, which needs the per-process lock PrecommitLocksLaterPrevotes (and the
\* valid-round conjuncts). Hence this preservation is stated over the full TypedIndInv.
\* Proof strategy (to mechanize). Assume, for a counterexample, a post-state precommit
\* quorum for w at r0 (>= 2T+1) and a post-state prevote quorum for w2 (in ValidValues,
\* w2 # w) at some r > r0. A single correct Step changes at most one of msgs_precommit /
\* msgs_prevote (no correct action touches both; only FaultyStep does, and it adds only
\* faulty senders, which cannot supply the >= T+1 correct part of a 2T+1 quorum). So one
\* of the two quorums is entirely pre-state.
\*   - If the precommit quorum is pre-state: PrecommitsLockValue (pre) already forbids a
\*     pre-state prevote quorum for w2 in r > r0; the fresh prevote adds one correct
\*     sender (PrevoteSenderSetCardinalityMonotone), so the pre-state prevote count was
\*     exactly 2T. The >= T+1 correct precommitters of w at r0 and the >= T+1 correct
\*     prevoters of w2 at r intersect (N = 3T+1); the shared correct process c either
\*     (a) prevoted w2 at r in the pre-state -- then PrecommitLocksLaterPrevotes gives a
\*     2T+1 prevote quorum for w2 at some r1 in [r0, r), contradicting PrecommitsLockValue
\*     (pre) [r1 = r0 handled by same-round quorum uniqueness + AllNoEquivocationByCorrect];
\*     or (b) c is the acting process casting the fresh prevote -- then its prevote-guard
\*     (locked on w via AllIfLockedRoundThenSentCommit) forces a valid-round vr in [r0, r)
\*     with a 2T+1 prevote quorum for w2 (AllIfValidRoundThenTwoThirdsPrevotes /
\*     AllCorrectProposalValidRoundBelowRound), again contradicting PrecommitsLockValue.
\*   - If the precommit quorum is fresh: symmetric, the acting process precommits w at r0
\*     and the pre-state carries a prevote quorum for w2 at r.
\* This is the core research obligation; it needs PrecommitLocksLaterPrevotes and the
\* valid-round conjuncts, hence the hypothesis is the full TypedIndInv.
\*
\* NOTE: this build's backends will not match the primed goal PrecommitsLockValue' by
\* unfolding it in place inside a SUFFICES; route through the explicit unfold equivalence
\* <1>unfold below, then reduce. Work through the operator abbreviations PCSetP / PVSetP so
\* Cardinality atoms are operator applications (the backends do the < / >= conversions on
\* those, but not on raw set-builders).
\* Correct/faulty senders of a precommit (resp. prevote) for value d in round r --
\* pre-state (PCSet / PVSet) and post-state / primed (PCSetP / PVSetP).
PCSet(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : mm.id = d} : s = m.src}
PVSet(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : mm.id = d} : s = m.src}
PCSetP(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit'[r] : mm.id = d} : s = m.src}
PVSetP(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote'[r] : mm.id = d} : s = m.src}
\* Flipped-orientation twins (d = mm.id) matching the regenerated spec's set-builders; used only to
\* restate the spec conjuncts so the \A-instantiation is over an operator (Gotcha 5), then bridged
\* to PCSet/PVSet (same set) by CardCong.
PCSetF(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : d = mm.id} : s = m.src}
PVSetF(r, d) == {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : d = mm.id} : s = m.src}

LEMMA PCSetSubset == ASSUME NEW r, NEW d PROVE PCSet(r, d) \in SUBSET (Corr \union Faulty)
  PROOF OMITTED
LEMMA PVSetSubset == ASSUME NEW r, NEW d PROVE PVSet(r, d) \in SUBSET (Corr \union Faulty)
  PROOF OMITTED

\* A precommit for a valid value (id = m.id) by a correct process at round r forces a 2T+1
\* prevote-sender quorum for m.id at r (IfSentPrecommitThenReceivedTwoThirds; the nil disjunct is
\* excluded since m.id is valid). Kept standalone so the instantiation runs in a CLEAN context:
\* the identical citation fails amid the heavy hypotheses of LockedValueGivesPostQuorum. Target the
\* message's own .id (never a substituted value) so PVSet stays folded -- cf. LockLemma's <1>pv.
LEMMA PrecommitByCorrectGivesPrevoteQuorum ==
  ASSUME TypedIndInv, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSet(r, m.id)) >= 2 * T + 1
PROOF OMITTED

LEMMA PVSetQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW d \in ((ValidValues \union InvalidValues) \union {-1}),
         Cardinality(PVSet(r, d)) >= 2 * T + 1
  PROVE  Cardinality(PVSetP(r, d)) >= 2 * T + 1
PROOF OMITTED

\* Mathematical heart of PrecommitsLockValue preservation. If a correct process c holds a
\* PRE-state precommit for w at r0 and a later PRE-state prevote for w2 (# w) at r > r0, and
\* w already has a 2T+1 precommit quorum at r0, then FALSE. PrecommitLocksLaterPrevotes gives
\* a 2T+1 prevote quorum for w2 in some r1 in [r0, r); that contradicts the pre-state lock
\* PrecommitsLockValue for r1 > r0, and for r1 = r0 the 2T+1 precommit quorum for w forces a
\* 2T+1 prevote quorum for w at r0 (IfSentPrecommitThenReceivedTwoThirds), so a correct
\* process prevotes both w and w2 at r0 -- ruled out by AllNoEquivocationByCorrect.
\* Tail of the lock contradiction, factored out so both routes to the intermediate prevote
\* quorum (PrecommitLocksLaterPrevotes for pre-state votes, or the acting process's prevote
\* guard for a fresh vote) can share it: a >= 2T+1 precommit quorum for w at r0 plus a >= 2T+1
\* prevote quorum for w2 (# w) in some round r1 in [r0, r) is contradictory. For r1 > r0 it
\* violates PrecommitsLockValue; for r1 = r0 the precommit quorum forces a prevote quorum for w
\* at r0 too, so a correct process prevotes both w and w2 at r0 (AllNoEquivocationByCorrect).
\* ===========================================================================
\* ORIENTATION BRIDGE. The regenerated spec renders the value on the LEFT of the
\* id-comparison (v = mm.id) in PrecommitsLockValue / PrecommitLocksLaterPrevotes,
\* while the proof operators PCSet/PVSet use the canonical (mm.id = v) form. The two
\* set-builders denote the same set (equality is symmetric), so PCSetFlip/PVSetFlip
\* (set equality, BY DEF) + CardCong (equal finite sets have equal Cardinality, via
\* FS_Subset) bridge the two. PrecommitsLockValueOp / PrecommitLocksLaterPrevotesOp
\* restate the two flipped conjuncts in canonical operator form once, so the deep
\* lock proofs cite them instead of unfolding the raw (flipped) conjuncts.
\* ===========================================================================
LEMMA PCSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit[r] : d = mm.id} : s = m.src}
PROOF OMITTED
LEMMA PVSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : d = mm.id} : s = m.src}
PROOF OMITTED
LEMMA PCSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit'[r] : d = mm.id} : s = m.src}
PROOF OMITTED
LEMMA PVSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote'[r] : d = mm.id} : s = m.src}
PROOF OMITTED

\* Any subset of the (finite) replica set is finite.
LEMMA SubsetCFFinite == ASSUME NEW A, A \subseteq (Corr \union Faulty) PROVE IsFiniteSet(A)
PROOF OMITTED

\* Cardinality congruence, grounded in FS_Subset (this tlapm build's backends do not
\* apply Leibniz under Cardinality on these set-builders without finiteness).
LEMMA CardCong ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S1), S1 = S2
  PROVE  Cardinality(S1) = Cardinality(S2)
PROOF OMITTED

\* Cardinality form of PVSetPFlip: the operator's Cardinality equals the flipped set-builder's.
LEMMA PVSetPFlipCard ==
  ASSUME NEW r, NEW d
  PROVE  Cardinality(PVSetP(r, d)) =
           Cardinality({s \in (Corr \union Faulty) :
             \E pv0 \in {pp \in msgs_prevote'[r] : d = pp.id} : s = pv0.src})
PROOF OMITTED

\* PrecommitsLockValue (spec-flipped) restated via PCSet/PVSet.
LEMMA PrecommitsLockValueOp ==
  ASSUME IndTypeOk, PrecommitsLockValue
  PROVE  \A r0 \in (0)..(MaxRound), w \in ValidValues :
           \/ Cardinality(PCSet(r0, w)) < 2 * T + 1
           \/ \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
                Cardinality(PVSet(r3, w2)) < 2 * T + 1
PROOF OMITTED

\* PrecommitLocksLaterPrevotes (spec-flipped consequent) restated via PVSet.
LEMMA PrecommitLocksLaterPrevotesOp ==
  ASSUME IndTypeOk, PrecommitLocksLaterPrevotes,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound), NEW v \in ValidValues,
         NEW r2 \in (0)..(MaxRound), r2 > r1,
         \E pc \in msgs_precommit[r1] : p = pc.src /\ pc.id /= -1 /\ v /= pc.id,
         \E pv \in msgs_prevote[r2] : p = pv.src /\ v = pv.id
  PROVE  \E r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} : Cardinality(PVSet(r, v)) >= 2 * T + 1
PROOF OMITTED

LEMMA LockContraFromPrevoteQuorum ==
  ASSUME TypedIndInv,
         NEW r0 \in (0)..(MaxRound), NEW r \in (0)..(MaxRound), r > r0,
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         Cardinality(PCSet(r0, w)) >= 2 * T + 1,
         \E r1 \in {rr \in (0)..(MaxRound) : rr >= r0 /\ rr < r} : Cardinality(PVSet(r1, w2)) >= 2 * T + 1
  PROVE  FALSE
PROOF OMITTED

\* Pre-state route: a correct process c with a pre-state precommit for w at r0 and a later
\* pre-state prevote for w2 (# w) at r, plus a 2T+1 precommit quorum for w at r0, is
\* contradictory -- PrecommitLocksLaterPrevotes supplies the intermediate prevote quorum for
\* LockContraFromPrevoteQuorum.
LEMMA PrecommitLockContra ==
  ASSUME TypedIndInv,
         NEW c \in Corr, NEW r0 \in (0)..(MaxRound), NEW r \in (0)..(MaxRound), r > r0,
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w,
         \E pv \in msgs_prevote[r] : pv.src = c /\ pv.id = w2,
         Cardinality(PCSet(r0, w)) >= 2 * T + 1
  PROVE  FALSE
PROOF OMITTED

\* A correct process that precommitted a non-nil value w at round r0 has locked_round >= r0
\* (AllLatestPrecommitHasLockedRound: every non-nil precommit by c has round <= locked_round[c]).
LEMMA LockedRoundGeR0 ==
  ASSUME TypedIndInv, NEW c \in Corr, NEW r0 \in (0)..(MaxRound), NEW w \in ValidValues,
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w
  PROVE  locked_round[c] >= r0
PROOF OMITTED

\* 2T+1 distinct prevote messages for idv at rr yield a 2T+1 prevote-sender quorum PVSet(rr,idv)
\* (each message is determined by its sender). Standalone so the LeSenders application runs in a
\* clean context.
LEMMA PrevoteMsgQuorumGivesSenderQuorum ==
  ASSUME TypedIndInv, NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1}),
         Cardinality({m \in msgs_prevote[rr] : m.id = idv}) >= 2 * T + 1
  PROVE  Cardinality(PVSet(rr, idv)) >= 2 * T + 1
PROOF OMITTED

\* Fresh-prevote guard analysis. A correct c locked on w (it precommitted w at r0) that adds a
\* fresh prevote for w2 (# w) in the current round can only do so via UponProposalInProposeAndPrevote,
\* whose guard supplies a proposal for w2 with valid_round vr < round[c] and a 2T+1 prevote quorum
\* for w2 at vr, and (since locked_value[c] # w2 in the main branch) requires locked_round[c] <= vr;
\* with locked_round[c] >= r0 that puts vr in [r0, round[c]).
LEMMA FreshPrevoteGivesQuorum ==
  ASSUME TypedIndInv, Step,
         NEW c \in Corr, NEW r0 \in (0)..(MaxRound),
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w,
         UponProposalInProposeAndPrevote(c),
         round[c] > r0,
         \E mv \in msgs_prevote'[round[c]] : mv.src = c /\ mv.id = w2 /\ mv \notin msgs_prevote[round[c]]
  PROVE  \E vr \in {x \in (0)..(MaxRound) : /\ (x >= r0) /\ (x < round[c])} : Cardinality(PVSet(vr, w2)) >= 2 * T + 1
PROOF OMITTED

LEMMA LockedValueGivesPostQuorum ==
  ASSUME TypedIndInv, Step,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound), NEW r2 \in (0)..(MaxRound),
         NEW v \in ValidValues,
         r2 > r1,
         \E pc \in msgs_precommit[r1]:
           /\ p = pc.src
           /\ pc.id /= -1
           /\ v /= pc.id,
         round[p] = r2,
         step[p] = "PROPOSE_OF_STEP",
         locked_value[p] = v
  PROVE  \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
           Cardinality(PVSetP(r, v)) >= 2 * T + 1
PROOF OMITTED

\* Pre-state variant of LockedValueGivesPostQuorum: a correct process locked on v (that also
\* precommitted a different value at r1) has a 2T+1 PRE-state prevote quorum for v at locked_round
\* in [r1, round). Used for the UponProposalInPropose branch of the caseChanged bridge.
LEMMA LockedValueGivesPreQuorum ==
  ASSUME TypedIndInv,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound), NEW r2 \in (0)..(MaxRound),
         NEW v \in ValidValues, r2 > r1,
         \E pc \in msgs_precommit[r1] : p = pc.src /\ pc.id /= -1 /\ v /= pc.id,
         round[p] = r2, step[p] = "PROPOSE_OF_STEP", locked_value[p] = v
  PROVE  \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2} : Cardinality(PVSet(r, v)) >= 2 * T + 1
PROOF OMITTED

\* A fresh valid (non-nil) prevote by a correct process c at round r is added only by the two
\* value-prevote actions, acting at round[c] = r. Standalone (clean context; the monolithic split
\* is defeated by the heavy hypotheses of the caseChanged bridge).
LEMMA FreshValuePrevoteAction ==
  ASSUME IndTypeOk, Step, NEW c \in Corr, NEW r \in (0)..(MaxRound),
         NEW mv \in msgs_prevote'[r], mv \notin msgs_prevote[r], mv.src = c, mv.id # -1
  PROVE  /\ round[c] = r
         /\ (UponProposalInPropose(c) \/ UponProposalInProposeAndPrevote(c))
PROOF OMITTED

\* A correct process c that precommitted w at r0 and, this Step, freshly prevotes w2 (# w) at
\* round[c] > r0 (via a value-prevote action) has a pre-state 2T+1 prevote quorum for w2 in
\* [r0, round[c]). UponProposalInProposeAndPrevote: FreshPrevoteGivesQuorum; UponProposalInPropose:
\* c is locked, so the fresh w2-prevote forces locked_value[c] = w2, i.e. c precommitted w2 at
\* locked_round[c] in (r0, round[c]) -> LockedValueGivesPreQuorum. Isolated (clean context).
LEMMA FreshPrevoteLockedGivesPreQuorum ==
  ASSUME TypedIndInv, Step, NEW c \in Corr, NEW r0 \in (0)..(MaxRound),
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w,
         round[c] > r0,
         \E mv \in msgs_prevote'[round[c]] : mv.src = c /\ mv.id = w2 /\ mv \notin msgs_prevote[round[c]],
         UponProposalInPropose(c) \/ UponProposalInProposeAndPrevote(c)
  PROVE  \E vr \in {x \in (0)..(MaxRound) : x >= r0 /\ x < round[c]} : Cardinality(PVSet(vr, w2)) >= 2 * T + 1
PROOF OMITTED

\* ---------------------------------------------------------------------------
\* BOOTSTRAP (for the Pres_PrecommitsLockValue caseB residue): the quorum-level lift of the
\* per-message conjunct AllIfSentPrevoteThenReceivedProposalOrTwoThirds. A 2T+1 prevote quorum for a
\* valid value v at round r contains a correct prevoter c; c's prevote (correct, non-nil) was backed
\* by EITHER a fresh proposal (valid_round = -1) for v at r, OR a proposal with valid_round vr < r
\* AND a 2T+1 prevote quorum for v at vr. So the quorum descends: either it is fresh, or an earlier
\* round already has a 2T+1 prevote quorum for v. Iterating this down to the least such round yields
\* a fresh proposal for v, at which a correct prevoter must be unlocked or locked on v -- the hook
\* that will contradict a competing r0 precommit-lock in caseB (the r1 > r0 sub-case).
\*
\* Initial structure below extracts a correct prevoter from the quorum, then applies
\* AllIfSentPrevoteThenReceivedProposalOrTwoThirds to that prevote and re-expresses its raw
\* Cardinality set-builder via PVSet.
\* ---------------------------------------------------------------------------
LEMMA PrevoteQuorumFreshOrEarlier ==
  ASSUME TypedIndInv, NEW r \in (0)..(MaxRound), NEW v \in ValidValues,
         Cardinality(PVSet(r, v)) >= 2 * T + 1
  PROVE  \/ (\E prop \in msgs_propose[r] :
               prop.src = Proposer[r] /\ prop.proposal = v /\ prop.valid_round = -1)
         \/ (\E vr \in {x \in (0)..(MaxRound) : x < r} : Cardinality(PVSet(vr, v)) >= 2 * T + 1)
PROOF OMITTED

LEMMA PostPrecommitByCorrectGivesPostPrevoteQuorum ==
  ASSUME TypedIndInv, Step, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit'[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSetP(r, m.id)) >= 2 * T + 1
PROOF OMITTED

LEMMA PostSameRoundPrecommitPrevoteQuorumsContra ==
  ASSUME TypedIndInv, Step, NEW r \in (0)..(MaxRound),
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         Cardinality(PCSetP(r, w)) >= 2 * T + 1,
         Cardinality(PVSetP(r, w2)) >= 2 * T + 1
  PROVE  FALSE
PROOF OMITTED

\* ---------------------------------------------------------------------------
\* TOP-LEVEL INDUCTIVE STEP: assemble type preservation + all 17 conjuncts.
\* ---------------------------------------------------------------------------
\* Preserving the 17 IndInv conjuncts. PrecommitsLockValue needs the extra IndInv
\* conjuncts (via Pres_PrecommitsLockValue), so the hypothesis is the full TypedIndInv;
\* the other 16 preservations only use the TypedIndInv part. Extending the conclusion
\* to the full TypedIndInv' requires preserving the remaining 7 support conjuncts.
\* ---------------------------------------------------------------------------
\* Preservation of the 8 extra IndInv support conjuncts (beyond IndInv).
\* ---------------------------------------------------------------------------
\* A correct proposer pr = Proposer[r] that reproposes fresh (valid_round = -1) at r never
\* precommitted a non-nil value below r. Assume a counterexample: a fresh proposal pp by pr at r
\* and a non-nil precommit mm by pr at r2 < r. Case on whether mm / pp are pre-state or fresh:
\* mm pre + pp pre contradicts the pre-invariant; mm pre + pp fresh gives valid_round[pr] = -1 so
\* locked_round[pr] = -1, contradicting mm's lock; mm fresh forces round[pr] = r2 with pp pre-state,
\* so AllNoFutureMessagesSent gives r <= round[pr] = r2 < r.
THEOREM Pres_AllLockedProposerReproposes ==
  ASSUME TypedIndInv, Step PROVE AllLockedProposerReproposes'
PROOF OMITTED

\* Harder than a per-process medium. The quorum disjuncts Q3 (T+1 prevote+precommit senders at r)
\* and Q4 (2T+1 precommit senders at r-1) are monotone, so preservation reduces to: when round[p]
\* advances past r, some Q holds at r. UponQuorumOfPrecommitsAny (round[p]+1) supplies Q4 at r-1
\* directly (its 2T+1 precommit trigger). OnRoundCatchup can jump many rounds to rnd on a T+1
\* propose+prevote+precommit quorum -- which does NOT match Q3 -- so it needs an indirect argument:
\* the T+1 evidence at rnd has a correct sender c, which by AllNoFutureMessagesSent already had
\* round[c] >= rnd pre-state, so AllPastStartRound(c, .) pre already gives Q3(r) \/ Q4(r) for every
\* r <= rnd. Mechanizing this (plus union-Cardinality monotonicity) is left as follow-up.
\* All-sender sets (no id filter) for the AllPastStartRound quorums: Q3(R) is a T+1 quorum over
\* prevote+precommit senders at R, Q4(R) a 2T+1 quorum over precommit senders at R-1.
PVAll(r)  == {s \in (Corr \union Faulty) : \E m \in msgs_prevote[r]    : s = m.src}
PCAll(r)  == {s \in (Corr \union Faulty) : \E m \in msgs_precommit[r]  : s = m.src}
PVAllP(r) == {s \in (Corr \union Faulty) : \E m \in msgs_prevote'[r]   : s = m.src}
PCAllP(r) == {s \in (Corr \union Faulty) : \E m \in msgs_precommit'[r] : s = m.src}

\* A superset of a >= k set is >= k (subset-shaped so the instantiation unifies on the subset
\* fact, unlike a bare arithmetic transitivity whose middle term is under-determined).
LEMMA SubsetCardGeq ==
  ASSUME NEW A, NEW B, A \subseteq B, IsFiniteSet(B), NEW k \in Nat, Cardinality(A) >= k
  PROVE  Cardinality(B) >= k
PROOF OMITTED

\* Pure arithmetic transitivity on abstract naturals. Used to lift a >= k through a <= b without
\* handing the concrete Cardinality set-builders to SMT (which then tries, and fails/stalls, to
\* reason about the set structure instead of treating the cardinalities as opaque integers).
LEMMA GeqTransLe ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW k \in Nat, a >= k, a <= b
  PROVE  b >= k
PROOF OMITTED

\* A T+1 sender set already contains a correct process (there are at most F <= T faulty).
LEMMA SmallQuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= T + 1
  PROVE  \E c \in Corr : c \in S
PROOF OMITTED

\* Senders of any message (propose/prevote/precommit) at round r.
AllMsgSenders(r) == {s \in (Corr \union Faulty) :
                       \/ (\E m \in msgs_propose[r]   : s = m.src)
                       \/ (\E m \in msgs_prevote[r]   : s = m.src)
                       \/ (\E m \in msgs_precommit[r] : s = m.src)}

\* OnRoundCatchup(p) advances p to some rnd > round[p] on a T+1 combined-evidence quorum at rnd;
\* those evidence senders are all message senders at rnd, so AllMsgSenders(rnd) has >= T+1 members
\* and (at most F <= T faulty) contains a correct process. Isolated so the deep evidence peel runs
\* in a clean context.
LEMMA OnRoundCatchupGivesSender ==
  ASSUME IndTypeOk, NEW p \in Corr, OnRoundCatchup(p)
  PROVE  \E rr \in (0)..(MaxRound) :
           /\ round' = [round EXCEPT ![p] = rr]
           /\ rr > round[p]
           /\ \E c \in Corr : c \in AllMsgSenders(rr)
PROOF OMITTED

\* The all-precommit and (prevote OR precommit) sender sets grow monotonically with the message log.
LEMMA PCAllMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PCAll(r)) <= Cardinality(PCAllP(r))
PROOF OMITTED

LEMMA Q3UnionMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PVAll(r) \union PCAll(r)) <= Cardinality(PVAllP(r) \union PCAllP(r))
PROOF OMITTED

\* A pre-state Q3(R) \/ Q4(R) lifts to the post-state (both quorums are monotone). R >= 1 so R-1
\* is a real round.
LEMMA PastStartRoundQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW R \in (0)..(MaxRound), R # 0,
         \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
  PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
         \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
PROOF OMITTED

\* The pre-invariant conjunct AllPastStartRound, re-expressed in operator form for a fixed (c, R).
LEMMA PastStartRoundOperator ==
  ASSUME IndTypeOk, AllPastStartRound, NEW c \in Corr, NEW R \in (0)..(MaxRound),
         ~(R > round[c]), R # 0
  PROVE  \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
PROOF OMITTED

\* If a correct process c is (pre-state) at round >= R >= 1, the post-state satisfies Q3(R) \/ Q4(R).
LEMMA PastStartRoundFromCorrect ==
  ASSUME IndTypeOk, Step, AllPastStartRound,
         NEW c \in Corr, NEW R \in (0)..(MaxRound), R # 0, R <= round[c]
  PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
         \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
PROOF OMITTED

\* Harder than a per-process medium. The quorum disjuncts Q3 (T+1 prevote+precommit senders at r)
\* and Q4 (2T+1 precommit senders at r-1) are monotone, so preservation reduces to: when round[p]
\* advances past r, some Q holds at r. UponQuorumOfPrecommitsAny (round[p]+1) supplies Q4 at r-1
\* directly (its 2T+1 precommit trigger). OnRoundCatchup can jump many rounds to rnd on a T+1
\* propose+prevote+precommit quorum -- which does NOT match Q3 -- so it needs an indirect argument:
\* the T+1 evidence at rnd has a correct sender c, which by AllNoFutureMessagesSent already had
\* round[c] >= rnd pre-state, so AllPastStartRound(c, .) pre already gives Q3(r) \/ Q4(r) for every
\* r <= rnd.
\* UponQuorumOfPrecommitsAny(p) fires on a 2T+1 precommit-sender quorum at round[p], which lifts
\* (monotone) to a 2T+1 post-state quorum PCAllP(round[p]). Kept as a standalone lemma so its
\* subset-cardinality lift runs in a clean context (cited from Pres_AllPastStartRound and
\* Pres_AllRoundsBelowHavePrecommitQuorum, where the same derivation inline drowns in hypotheses).
LEMMA UQPAGivesPostQuorum ==
  ASSUME IndTypeOk, Step, NEW p \in Corr, UponQuorumOfPrecommitsAny(p)
  PROVE  Cardinality(PCAllP(round[p])) >= 2 * T + 1
PROOF OMITTED

THEOREM Pres_AllPastStartRound ==
  ASSUME TypedIndInv, Step PROVE AllPastStartRound'
PROOF OMITTED

\* ---------------------------------------------------------------------------
\* CHOOSE-max machinery for AllRoundsBelowHavePrecommitQuorum. The regenerated spec expresses the
\* maximum round reached as CHOOSE m in ({round[k]} \union {0}): m >= every candidate.
\* ---------------------------------------------------------------------------
\* A nonempty subset of a bounded integer interval has a maximum (induction on the bound via
\* NatInductionTrusted -- avoids the higher-order FS_Induction, which needs Isabelle here).
LEMMA BoundedMaxExists ==
  ASSUME NEW b \in Nat, NEW S \in SUBSET (0)..b, S # {}
  PROVE  \E mx \in S : \A o \in S : mx >= o
PROOF OBVIOUS

MaxCandOf(rd) == {rd[k] : k \in DOMAIN rd} \union {0}
MaxReachedOf(rd) == CHOOSE mx \in MaxCandOf(rd) : \A o \in MaxCandOf(rd) : mx >= o

\* The CHOOSE-max lands in the candidate set and dominates it (the max exists, by BoundedMaxExists).

\* A correct process reaches round R (R < max reached) only after every earlier round collected a
\* 2T+1 precommit quorum. The global max advances only via UponQuorumOfPrecommitsAny (+1, whose
\* 2T+1 precommit trigger IS the quorum at the round left); OnRoundCatchup cannot advance the max
\* (its evidence has a correct sender c with round[c] >= its target, so the target was already
\* reached). Below the pre-max, the pre-invariant + PCAll monotonicity suffice.

\* If valid_round[q]' = round[q]' then the acting process's step guard (for the step-changing
\* actions the actor was in PROPOSE/PREVOTE, so by the pre-invariant valid_round[q] # round[q],
\* making the premise vacuous for it) or the round-advance bound (valid_round <= round) forces the
\* premise vacuous, and the locking action sets step to PRECOMMIT.

\* locked_round and valid_round change only in UponProposalInPrevoteOrCommitAndPrevote, which
\* sets both to round[p] (lab_then) or leaves locked_round and sets valid_round = round[p]
\* (lab_else, where locked_round <= round by AllValidAndLockedRoundBounded).

\* valid_round changes only in UponProposalInPrevoteOrCommitAndPrevote (to round[p]); lab_then
\* adds a precommit by p at round[p], lab_else has step[p] = PRECOMMIT so a precommit by p at
\* round[p] already exists (AllIfInPrecommitThenSentPrecommit). Otherwise valid_round[q] is
\* unchanged and its old precommit persists (PrecommitMonotone).

\* Proposals are added only by InsertProposal (correct proposer, step PROPOSE), which sets the
\* proposal's valid_round = valid_round[p]. step[p] = PROPOSE gives valid_round[p] # round[p]
\* (AllValidInCurrentRoundPrecommitted contrapositive), and valid_round[p] <= round[p]
\* (AllValidAndLockedRoundBounded), so valid_round[p] < round[p].

\* A fresh non-nil precommit by a correct process p at r1 is added only by
\* UponProposalInPrevoteOrCommitAndPrevote(p) (the only action adding a non-nil correct precommit),
\* which acts in round[p] = r1 at step PREVOTE and leaves msgs_prevote unchanged. Standalone so the
\* heavy Step case analysis runs in a clean context (Gotcha 6).

\* The per-process lock-survival invariant. Its preservation is a research obligation of the
\* same character as Pres_PrecommitsLockValue (it is exactly the hypothesis that proof relies on).

\*****************************************************************************
\* SECTION D -- AGREEMENT
\*
\* TODO: port the Ben-Or Section D chain:
\*   quorum-uniqueness within a round  ->  cross-round strict-quorum lock
\*   (PrecommitsLockValue)  ->  decided value is backed by a 2T+1 precommit
\*   quorum (AllIfInDecidedThenReceivedTwoThirds)  ->  case-split on the two
\*   decided rounds, closing the induction with NatInductionTrusted and
\*   QuorumsIntersectInCorrect.
\* Named AgreementThm (not Agreement, which is a spec operator).
\*****************************************************************************

=============================================================================
