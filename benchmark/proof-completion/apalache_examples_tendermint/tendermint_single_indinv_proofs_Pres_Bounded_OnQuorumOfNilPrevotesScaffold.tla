------------------- MODULE tendermint_single_indinv_proofs_Pres_Bounded_OnQuorumOfNilPrevotesScaffold -------------------

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

=============================================================================
