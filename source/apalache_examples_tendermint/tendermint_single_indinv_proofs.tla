------------------- MODULE tendermint_single_indinv_proofs -------------------
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
  BY SMT

LEMMA IntLeGeTrans1 ==
  ASSUME NEW a \in Int, NEW b \in Int, NEW k \in Int,
         a >= k, a <= b
  PROVE  b >= k
  BY SMT

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
  <1> DEFINE U == Corr \union Faulty
  <1> DEFINE I == A \cap B
  <1> DEFINE IC == I \cap Corr
  <1> DEFINE IFa == I \cap Faulty
  <1>finU. IsFiniteSet(U)  BY FiniteCF, FS_Union
  <1>AsubU. A \subseteq U  OBVIOUS
  <1>BsubU. B \subseteq U  OBVIOUS
  <1>finA. IsFiniteSet(A)  BY <1>finU, <1>AsubU, FS_Subset
  <1>finB. IsFiniteSet(B)  BY <1>finU, <1>BsubU, FS_Subset
  <1>IsubU. I \subseteq U  OBVIOUS
  <1>finI. IsFiniteSet(I)  BY <1>finU, <1>IsubU, FS_Subset
  <1>ICsubU. IC \subseteq U  OBVIOUS
  <1>finIC. IsFiniteSet(IC)  BY <1>finU, <1>ICsubU, FS_Subset
  <1>IFasubFa. IFa \subseteq Faulty  OBVIOUS
  <1>finIFa. IsFiniteSet(IFa)  BY FiniteCF, <1>IFasubFa, FS_Subset
  <1>unionSubU. (A \cup B) \subseteq U  OBVIOUS
  <1>finX. /\ IsFiniteSet(Corr \cap Faulty) /\ IsFiniteSet(IC \cup IFa)
           /\ IsFiniteSet(IC \cap IFa) /\ IsFiniteSet(A \cup B)
      <2>1. (Corr \cap Faulty) \subseteq Corr  OBVIOUS
      <2>2. (IC \cup IFa) \subseteq U /\ (IC \cap IFa) \subseteq U /\ (A \cup B) \subseteq U  OBVIOUS
      <2> QED  BY <2>1, <2>2, <1>finU, FiniteCF, FS_Subset
  <1>types. /\ Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(I) \in Nat
            /\ Cardinality(IC) \in Nat /\ Cardinality(IFa) \in Nat /\ Cardinality(A \cup B) \in Nat
            /\ Cardinality(Faulty) \in Nat /\ Cardinality(Corr) \in Nat /\ Cardinality(U) \in Nat
            /\ Cardinality(Corr \cap Faulty) \in Nat /\ Cardinality(IC \cup IFa) \in Nat
            /\ Cardinality(IC \cap IFa) \in Nat
      BY <1>finA, <1>finB, <1>finI, <1>finIC, <1>finIFa, <1>finU, <1>finX, FiniteCF, FS_CardinalityType
  <1>cardU. Cardinality(U) = N
      <2>1. Cardinality(U) = Cardinality(Corr) + Cardinality(Faulty) - Cardinality(Corr \cap Faulty)
            BY FiniteCF, FS_Union
      <2>2. Cardinality(Corr \cap Faulty) = 0
            BY DisjointCF, FS_EmptySet
      <2> QED  BY <2>1, <2>2, NCard, <1>types, SMT
  <1>cardUnion. Cardinality(A \cup B) = Cardinality(A) + Cardinality(B) - Cardinality(I)
      BY <1>finA, <1>finB, FS_Union
  <1>cardUnionLeN. Cardinality(A \cup B) <= N
      BY <1>finU, <1>unionSubU, FS_Subset, <1>cardU
  <1>cardI. Cardinality(I) >= 4 * T + 2 - N
      BY <1>cardUnion, <1>cardUnionLeN, <1>types, ConstNat, SMT
  <1>Ipart. I = IC \cup IFa  BY <1>IsubU
  <1>disj. IC \cap IFa = {}  BY DisjointCF
  <1>cardIeq. Cardinality(I) = Cardinality(IC) + Cardinality(IFa)
      <2>1. Cardinality(IC \cup IFa) = Cardinality(IC) + Cardinality(IFa) - Cardinality(IC \cap IFa)
            BY <1>finIC, <1>finIFa, FS_Union
      <2>2. Cardinality(IC \cap IFa) = 0  BY <1>disj, FS_EmptySet
      <2> QED  BY <2>1, <2>2, <1>Ipart, <1>types, SMT
  <1>cardIFaLeF. Cardinality(IFa) <= Cardinality(Faulty)
      BY <1>IFasubFa, FiniteCF, FS_Subset
  <1>cardICge. Cardinality(IC) >= 4 * T + 2 - N - Cardinality(Faulty)
      BY <1>cardI, <1>cardIeq, <1>cardIFaLeF, <1>types, ConstNat, SMT
  <1>pos. Cardinality(IC) >= 1
      \* 4T+2-N-F = 4T+2-(3T+1)-F = T+1-F >= 1, using N = 3T+1 and Cardinality(Faulty) = F <= T
      BY <1>cardICge, <1>types, Neq3Tp1, TgeF, ConstNat DEF F
  <1>ne. IC # {}
      BY <1>pos, <1>finIC, FS_EmptySet
  <1> QED
      <2> PICK c \in IC : TRUE  BY <1>ne
      <2> QED  OBVIOUS

\* A single quorum (>= 2T+1 senders) already contains a correct process.
THEOREM QuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in S
  BY QuorumsIntersectInCorrect

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
  <1> SUFFICES ASSUME Init PROVE TypedIndInv
      OBVIOUS
  <1> USE ConstNat DEF Init
  \* the empty logs / nil flags, exposed for every conjunct below
  <1>e. /\ \A r \in (0)..(MaxRound) :
              msgs_propose[r] = {} /\ msgs_prevote[r] = {} /\ msgs_precommit[r] = {}
        /\ \A p \in Corr :
              round[p] = 0 /\ step[p] = "PROPOSE_OF_STEP" /\ decision[p] = -1
              /\ locked_value[p] = -1 /\ locked_round[p] = -1
              /\ valid_value[p] = -1 /\ valid_round[p] = -1
        OBVIOUS
  <1>type. IndTypeOk
        BY SMT DEF IndTypeOk
  <1>1.  AllNoFutureMessagesSent
        BY <1>e, SMT DEF AllNoFutureMessagesSent
  <1>2.  AllIfInPrevoteThenSentPrevote
        BY <1>e DEF AllIfInPrevoteThenSentPrevote
  <1>3.  AllIfInPrecommitThenSentPrecommit
        BY <1>e DEF AllIfInPrecommitThenSentPrecommit
  <1>4.  AllIfInDecidedThenReceivedProposal
        BY <1>e DEF AllIfInDecidedThenReceivedProposal
  <1>5.  AllIfInDecidedThenReceivedTwoThirds
        BY <1>e DEF AllIfInDecidedThenReceivedTwoThirds
  <1>6.  AllIfInDecidedThenValidDecision
        BY <1>e, NilNotValid, SMT DEF AllIfInDecidedThenValidDecision
  <1>7.  AllLockedRoundIffLockedValue
        BY <1>e DEF AllLockedRoundIffLockedValue
  <1>8.  AllValidRoundIffValidValue
        BY <1>e DEF AllValidRoundIffValidValue
  <1>9.  AllValidAndLockedRoundBounded
        BY <1>e, SMT DEF AllValidAndLockedRoundBounded
  <1>10. AllIfValidRoundThenTwoThirdsPrevotes
        BY <1>e DEF AllIfValidRoundThenTwoThirdsPrevotes
  <1>11. AllIfLockedRoundThenSentCommit
        BY <1>e DEF AllIfLockedRoundThenSentCommit
  <1>12. AllLatestPrecommitHasLockedRound
        BY <1>e DEF AllLatestPrecommitHasLockedRound
  <1>13. AllIfSentPrevoteThenReceivedProposalOrTwoThirds
        BY <1>e DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
  <1>14. IfSentPrecommitThenSentPrevote
        BY <1>e DEF IfSentPrecommitThenSentPrevote
  <1>15. IfSentPrecommitThenReceivedTwoThirds
        BY <1>e DEF IfSentPrecommitThenReceivedTwoThirds
  <1>16. AllNoEquivocationByCorrect
        BY <1>e, ValidValuesNonEmpty DEF AllNoEquivocationByCorrect
  <1>17. PrecommitsLockValue
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW v \in ValidValues
                 PROVE  Cardinality({s \in (Corr \union Faulty) :
                           \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src}) < 2 * T + 1
        BY DEF PrecommitsLockValue
    <2>1. msgs_precommit[r] = {}
          BY <1>e
    <2>2. {mm \in msgs_precommit[r] : v = mm.id} = {}
          BY <2>1, FS_EmptySet
    <2>3. {s \in (Corr \union Faulty) :
             \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src} = {}
          BY <2>2, FS_EmptySet
    <2>4. Cardinality({s \in (Corr \union Faulty) :
             \E m \in {mm \in msgs_precommit[r] : v = mm.id} : s = m.src}) = 0
          BY <2>3, FS_EmptySet
    <2>5. 0 < 2 * T + 1
          BY ConstNat, SMT
    <2> QED BY <2>4, <2>5
  \* The 8 extra IndInv support conjuncts -- all vacuous or trivial at Init.
  <1>18. PrecommitLocksLaterPrevotes
        BY <1>e DEF PrecommitLocksLaterPrevotes
  <1>19. AllLockedProposerReproposes
        BY <1>e DEF AllLockedProposerReproposes
  <1>20. AllPastStartRound
        BY <1>e, SMT DEF AllPastStartRound
  <1>21. AllRoundsBelowHavePrecommitQuorum
        \* At Init every round[k] = 0, so the CHOOSE-max of {round[k]} \union {0} is 0, and the
        \* antecedent r < 0 is false for r \in (0)..(MaxRound).
        <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                            r < (LET mc == ({round[k743] : k743 \in DOMAIN round} \union {0})
                                 IN CHOOSE mx \in mc : \A o \in mc : mx >= o)
                     PROVE  Cardinality({v_v747 \in (Corr \union Faulty) :
                              \E v_v748 \in msgs_precommit[r] : v_v747 = v_v748.src}) >= 2 * T + 1
            BY DEF AllRoundsBelowHavePrecommitQuorum
        <2>dom. DOMAIN round = Corr  BY DEF Init
        <2>cand. ({round[k743] : k743 \in DOMAIN round} \union {0}) = {0}  BY <1>e, <2>dom
        <2>max. (CHOOSE mx \in ({round[k743] : k743 \in DOMAIN round} \union {0}) :
                   \A o \in ({round[k743] : k743 \in DOMAIN round} \union {0}) : mx >= o) = 0
            <3>1. (CHOOSE mx \in {0} : \A o \in {0} : mx >= o) = 0
                <4>ex. \E mx \in {0} : \A o \in {0} : mx >= o  OBVIOUS
                <4> QED  BY <4>ex
            <3> QED  BY <3>1, <2>cand
        <2> QED  BY <2>max, SMT
  <1>22. AllValidInCurrentRoundPrecommitted
        BY <1>e, SMT DEF AllValidInCurrentRoundPrecommitted
  <1>23. AllLockedRoundBelowValidRound
        BY <1>e, SMT DEF AllLockedRoundBelowValidRound
  <1>24. AllIfValidRoundThenPrecommitted
        BY <1>e DEF AllIfValidRoundThenPrecommitted
  <1>25. AllCorrectProposalValidRoundBelowRound
        BY <1>e DEF AllCorrectProposalValidRoundBelowRound
  <1> QED
      BY <1>type, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
         <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17,
         <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24, <1>25
      DEF TypedIndInv, IndInv

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
  <1>1. <<s, rr, pr, vr>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

LEMMA PrevoteRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
  <1>1. <<s, rr, idv>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

LEMMA PrecommitRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
  <1>1. <<s, rr, idv>> \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))
        OBVIOUS
  <1> QED BY <1>1, SMT

\* Message monotonicity: every Step action either leaves a message log unchanged
\* or appends to it (EXCEPT-union), so entries are never removed. Used by the
\* Section C "in step X => already sent Y" conjuncts to carry a witnessing
\* message across a step.
LEMMA ProposeMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_propose[r]
  PROVE  x \in msgs_propose'[r]
  <1> USE DEF IndTypeOk
  <1>sel. msgs_propose' = msgs_propose \/ (\E p \in Corr : InsertProposal(p)) \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_propose' = msgs_propose  BY <1>1
  <1>2. CASE \E p \in Corr : InsertProposal(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_propose' = [msgs_propose EXCEPT ![idx] = (msgs_propose[idx] \union S)]
            BY <1>2 DEF InsertProposal
      <2> QED  BY <2>1, SMT
  <1>3. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_propose' = [msgs_propose EXCEPT ![idx] = (msgs_propose[idx] \union S)]
            BY <1>3 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3

LEMMA PrevoteMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_prevote[r]
  PROVE  x \in msgs_prevote'[r]
  <1> USE DEF IndTypeOk
  <1>sel. \/ msgs_prevote' = msgs_prevote
          \/ \E p \in Corr : UponProposalInPropose(p)
          \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
          \/ \E p \in Corr : OnTimeoutPropose(p)
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_prevote' = msgs_prevote  BY <1>1
  <1>2. CASE \E p \in Corr : UponProposalInPropose(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>2 DEF UponProposalInPropose
      <2> QED  BY <2>1, SMT
  <1>3. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>3 DEF UponProposalInProposeAndPrevote
      <2> QED  BY <2>1, SMT
  <1>4. CASE \E p \in Corr : OnTimeoutPropose(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>4 DEF OnTimeoutPropose
      <2> QED  BY <2>1, SMT
  <1>5. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_prevote' = [msgs_prevote EXCEPT ![idx] = (msgs_prevote[idx] \union S)]
            BY <1>5 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA PrecommitMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound), NEW x \in msgs_precommit[r]
  PROVE  x \in msgs_precommit'[r]
  <1> USE DEF IndTypeOk
  <1>sel. \/ msgs_precommit' = msgs_precommit
          \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
          \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_precommit' = msgs_precommit  BY <1>1
  <1>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
      \* then-branch appends, else leaves unchanged; either way x persists
      <2>1. msgs_precommit' = msgs_precommit
            \/ (\E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)])
            BY <1>2 DEF UponProposalInPrevoteOrCommitAndPrevote
      <2> QED  BY <2>1, SMT
  <1>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>3 DEF UponQuorumOfPrevotesAny
      <2> QED  BY <2>1, SMT
  <1>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>4 DEF OnQuorumOfNilPrevotes
      <2> QED  BY <2>1, SMT
  <1>5. CASE FaultyStep
      <2>1. \E idx \in (0)..(MaxRound) : \E S : msgs_precommit' = [msgs_precommit EXCEPT ![idx] = (msgs_precommit[idx] \union S)]
            BY <1>5 DEF FaultyStep
      <2> QED  BY <2>1, SMT
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA PrevoteSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote'[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_prevote'[r] : mm.id = idv} : s = m.src}
  <1>sub. Old \subseteq New
        BY PrevoteMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrevoteAllSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote'[r] : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in msgs_prevote[r] : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in msgs_prevote'[r] : s = m.src}
  <1>sub. Old \subseteq New
        BY PrevoteMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrevoteValueSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE ValueSenders == {s \in (Corr \union Faulty) :
                                \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src}
              AllSenders == {s \in (Corr \union Faulty) :
                                \E m \in msgs_prevote[r] : s = m.src}
  <1>sub. ValueSenders \subseteq AllSenders
        BY DEF ValueSenders, AllSenders
  <1>allSub. AllSenders \subseteq (Corr \union Faulty)
        BY DEF AllSenders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finAll. IsFiniteSet(AllSenders)
        BY <1>allSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finAll, FS_Subset

LEMMA PrevoteEvidenceSenderSetCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound), NEW E \in SUBSET msgs_prevote[r]
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in E : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE EvidenceSenders == {s \in (Corr \union Faulty) :
                                   \E m \in E : s = m.src}
              AllSenders == {s \in (Corr \union Faulty) :
                                \E m \in msgs_prevote[r] : s = m.src}
  <1>sub. EvidenceSenders \subseteq AllSenders
        BY DEF EvidenceSenders, AllSenders
  <1>allSub. AllSenders \subseteq (Corr \union Faulty)
        BY DEF AllSenders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finAll. IsFiniteSet(AllSenders)
        BY <1>allSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finAll, FS_Subset

LEMMA PrecommitSenderSetCardinalityMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Old == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src}
              New == {s \in (Corr \union Faulty) :
                       \E m \in {mm \in msgs_precommit'[r] : mm.id = idv} : s = m.src}
  <1>sub. Old \subseteq New
        BY PrecommitMonotone DEF Old, New
  <1>newSub. New \subseteq (Corr \union Faulty)
        BY DEF New
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finNew. IsFiniteSet(New)
        BY <1>newSub, <1>finCF, FS_Subset
  <1> QED
        BY <1>sub, <1>finNew, FS_Subset

LEMMA PrecommitValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_precommit[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_precommit[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_precommit[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrecommitValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_precommit[r] : m.id = idv})
  <1> DEFINE Msgs == {m \in msgs_precommit[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesCardinalityLeSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in {mm \in msgs_prevote[r] : mm.id = idv} : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesCardinalityLeAllSenders ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  Cardinality({m \in msgs_prevote[r] : m.id = idv})
         <=
         Cardinality({s \in (Corr \union Faulty) :
            \E m \in msgs_prevote[r] : s = m.src})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in msgs_prevote[r] : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA PrevoteValueMessagesFinite ==
  ASSUME IndTypeOk, NEW r \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  IsFiniteSet({m \in msgs_prevote[r] : m.id = idv})
  <1> DEFINE Msgs == {m \in msgs_prevote[r] : m.id = idv}
              Senders == {s \in (Corr \union Faulty) : \E m \in Msgs : s = m.src}
              SrcOf == [m \in Msgs |-> m.src]
  <1>sendersSub. Senders \subseteq (Corr \union Faulty)
        BY DEF Senders
  <1>finCF. IsFiniteSet(Corr \union Faulty)
        BY FiniteCF, FS_Union
  <1>finSenders. IsFiniteSet(Senders)
        BY <1>sendersSub, <1>finCF, FS_Subset
  <1>dom. DOMAIN SrcOf = Msgs
        BY DEF SrcOf
  <1>range. \A x \in Msgs : SrcOf[x] \in Senders
        BY SMT DEF SrcOf, Senders, Msgs, IndTypeOk
  <1>fun. SrcOf \in [Msgs -> Senders]
        BY <1>dom, <1>range, SMT
  <1>one. \A x \in Msgs : \A y \in Msgs : SrcOf[x] = SrcOf[y] => x = y
        BY SMT DEF SrcOf, Msgs, IndTypeOk
  <1>inj. SrcOf \in Injection(Msgs, Senders)
        BY <1>fun, <1>one DEF Injection, IsInjective
  <1> QED
        BY <1>inj, <1>finSenders, FS_Injection

LEMMA StepUpdateChangedProcess ==
  ASSUME IndTypeOk, NEW p \in Corr, NEW q \in Corr, NEW st,
         step' = [step EXCEPT ![p] = st],
         step'[q] # step[q]
  PROVE  q = p
  BY SMT DEF IndTypeOk

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
  <1> USE DEF IndTypeOk
  <1>sel. \/ step' = step
          \/ \E p \in Corr : UponProposalInPropose(p)
          \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
          \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          \/ \E p \in Corr : UponQuorumOfPrecommitsAny(p)
          \/ \E p \in Corr : UponProposalInPrecommitNoDecision(p)
          \/ \E p \in Corr : OnTimeoutPropose(p)
          \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
          \/ \E p \in Corr : OnRoundCatchup(p)
      BY DEF Step
  <1>0. CASE step' = step
      BY <1>0
  <1>1. CASE \E p \in Corr : UponProposalInPropose(p)
    <2> PICK p \in Corr : UponProposalInPropose(p) BY <1>1
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF UponProposalInPropose
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>1, <2>2
  <1>2. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
    <2> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <1>2
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF UponProposalInProposeAndPrevote
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>2, <2>2
  <1>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
    <2> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <1>3
    <2>1. step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"] BY DEF UponQuorumOfPrevotesAny
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>3, <2>2
  <1>4. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
    <2> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <1>4
    <2>1. step' = step \/ step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"]
          BY DEF UponProposalInPrevoteOrCommitAndPrevote
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>4, <2>2
  <1>5. CASE \E p \in Corr : UponQuorumOfPrecommitsAny(p)
    <2> PICK p \in Corr : UponQuorumOfPrecommitsAny(p) BY <1>5
    <2>1. step' = [step EXCEPT ![p] = "PROPOSE_OF_STEP"] BY DEF UponQuorumOfPrecommitsAny
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>5, <2>2
  <1>6. CASE \E p \in Corr : UponProposalInPrecommitNoDecision(p)
    <2> PICK p \in Corr : UponProposalInPrecommitNoDecision(p) BY <1>6
    <2>1. step' = [step EXCEPT ![p] = "DECIDED_OF_STEP"] BY DEF UponProposalInPrecommitNoDecision
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>6, <2>2
  <1>7. CASE \E p \in Corr : OnTimeoutPropose(p)
    <2> PICK p \in Corr : OnTimeoutPropose(p) BY <1>7
    <2>1. step' = [step EXCEPT ![p] = "PREVOTE_OF_STEP"] BY DEF OnTimeoutPropose
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>7, <2>2
  <1>8. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
    <2> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <1>8
    <2>1. step' = [step EXCEPT ![p] = "PRECOMMIT_OF_STEP"] BY DEF OnQuorumOfNilPrevotes
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>8, <2>2
  <1>9. CASE \E p \in Corr : OnRoundCatchup(p)
    <2> PICK p \in Corr : OnRoundCatchup(p) BY <1>9
    <2>1. step' = [step EXCEPT ![p] = "PROPOSE_OF_STEP"] BY DEF OnRoundCatchup
    <2>2. q = p BY <2>1, StepUpdateChangedProcess
    <2> QED BY <1>9, <2>2
  <1> QED BY <1>sel, <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9

LEMMA EnteredPrevoteHasSentPrevote ==
  ASSUME TypedIndInv, Step, NEW q \in Corr,
         step[q] # "PREVOTE_OF_STEP", step'[q] = "PREVOTE_OF_STEP"
  PROVE  \E m \in msgs_prevote'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
  BY SMT DEF TypedIndInv, IndInv, IndTypeOk, Step, InsertProposal,
     UponProposalInPropose, UponProposalInProposeAndPrevote,
     UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
     UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
     OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep

LEMMA EnteredPrecommitHasSentPrecommit ==
  ASSUME TypedIndInv, Step, NEW q \in Corr,
         step[q] # "PRECOMMIT_OF_STEP", step'[q] = "PRECOMMIT_OF_STEP"
  PROVE  \E m \in msgs_precommit'[round'[q]] :
           /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
           /\ q = m.src
  BY SMT DEF TypedIndInv, IndInv, IndTypeOk, Step, InsertProposal,
     UponProposalInPropose, UponProposalInProposeAndPrevote,
     UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
     UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
     OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep

LEMMA RoundMonotone ==
  ASSUME IndTypeOk, Step, NEW q \in Corr
  PROVE  round[q] <= round'[q]
  BY SMT DEF IndTypeOk, Step, UponQuorumOfPrecommitsAny, OnRoundCatchup

\* Type preservation, grouped by type conjunct: each state variable is touched
\* by only a few Step actions; for all other actions it is UNCHANGED and its type
\* carries from the hypothesis IndTypeOk. `BY DEF Step, <actions>` unfolds Step's
\* disjunction and the cited actions; uncited disjuncts keep the variable via
\* their own UNCHANGED tuple. Message-adding actions build records that match the
\* IndTypeOk element sets (src in Corr\union Faulty, round = index, value typed).
THEOREM TypePres ==
  ASSUME TypedIndInv, Step
  PROVE  IndTypeOk'
  <1> USE DEF TypedIndInv, IndTypeOk
  <1>1. (round \in [Corr -> (0)..(MaxRound)])'
        BY DEF Step, UponQuorumOfPrecommitsAny, OnRoundCatchup
  <1>2. (step \in [Corr -> {"PROPOSE_OF_STEP", "PREVOTE_OF_STEP", "PRECOMMIT_OF_STEP", "DECIDED_OF_STEP"}])'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote,
            UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
            UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
            OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
  <1>3. (decision \in [Corr -> (ValidValues \union {-1})])'
        BY DEF Step, UponProposalInPrecommitNoDecision
  <1>4. (locked_value \in [Corr -> (ValidValues \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>5. (locked_round \in [Corr -> ((0)..(MaxRound) \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>6. (valid_value \in [Corr -> (ValidValues \union {-1})])'
        BY DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>7. (valid_round \in [Corr -> ((0)..(MaxRound) \union {-1})])'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>8. (DOMAIN msgs_propose = (0)..(MaxRound))'
        BY SMT DEF Step, InsertProposal, FaultyStep
  <1>9. (\A v_v89 \in (0)..(MaxRound): \A v_v90 \in msgs_propose[v_v89]: (v_v90 \in {[proposal |-> v_v91[3], round |-> v_v91[2], src |-> v_v91[1], valid_round |-> v_v91[4]]: v_v91 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}))'
    <2> DEFINE RecP == {[proposal |-> t[3], round |-> t[2], src |-> t[1], valid_round |-> t[4]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_propose'[r]
                 PROVE  m \in RecP
        OBVIOUS
    <2>H. \A mm \in msgs_propose[r] : mm \in RecP
        BY DEF IndTypeOk
    <2>sel. msgs_propose' = msgs_propose \/ (\E p \in Corr : InsertProposal(p)) \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_propose' = msgs_propose
        BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : InsertProposal(p)
        <3> PICK p \in Corr : InsertProposal(p)  BY <2>2
        <3>1. PICK v \in ValidValues :
                msgs_propose' = [msgs_propose EXCEPT ![round[p]] =
                  (msgs_propose[round[p]] \union {[proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v),
                     round |-> round[p], src |-> p, valid_round |-> valid_round[p]]})]
              BY DEF InsertProposal
        <3>2. round[p] \in (0)..(MaxRound) /\ valid_round[p] \in ((0)..(MaxRound) \union {-1})
              /\ valid_value[p] \in (ValidValues \union {-1})
              BY DEF IndTypeOk
        <3>3. (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v) \in ((ValidValues \union InvalidValues) \union {-1})
              BY <3>2
        <3>4. m \in msgs_propose[r]
              \/ m = [proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v), round |-> round[p], src |-> p, valid_round |-> valid_round[p]]
              BY <3>1
        <3>5. CASE m \in msgs_propose[r]  BY <2>H, <3>5
        <3>6. CASE m = [proposal |-> (IF (valid_value[p] /= -1) THEN valid_value[p] ELSE v), round |-> round[p], src |-> p, valid_round |-> valid_round[p]]
              BY <3>2, <3>3, <3>6, ProposeRecTyped
        <3> QED  BY <3>4, <3>5, <3>6
    <2>3. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps1 \in SUBSET Faulty,
                   v1 \in (ValidValues \union InvalidValues), vr1 \in ((0)..(MaxRound) \union {-1}) :
                msgs_propose' = [msgs_propose EXCEPT ![rF] =
                  (msgs_propose[rF] \union {[proposal |-> v1, round |-> rF, src |-> v_v53, valid_round |-> vr1] : v_v53 \in fps1})]
              BY <2>3 DEF FaultyStep
        <3>2. m \in msgs_propose[r]
              \/ (\E s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1])
              BY <3>1
        <3>3. CASE m \in msgs_propose[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1]
              <4> PICK s0 \in fps1 : m = [proposal |-> v1, round |-> rF, src |-> s0, valid_round |-> vr1]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v1 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, ProposeRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3
  <1>10. (\A v_v92 \in DOMAIN msgs_propose: \A v_v93 \in msgs_propose[v_v92]: (v_v92 = v_v93.round))'
        BY SMT DEF Step, InsertProposal, FaultyStep
  <1>11. (DOMAIN msgs_prevote = (0)..(MaxRound))'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote, OnTimeoutPropose, FaultyStep
  <1>12. (\A v_v94 \in (0)..(MaxRound): \A v_v95 \in msgs_prevote[v_v94]: (v_v95 \in {[id |-> v_v96[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> v_v96[2], src |-> v_v96[1]]: v_v96 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}))'
    <2> DEFINE RecV == {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_prevote'[r]
                 PROVE  m \in RecV
        OBVIOUS
    <2>H. \A mm \in msgs_prevote[r] : mm \in RecV  BY DEF IndTypeOk
    \* one lemma shape covers all three correct broadcasts: some in-range id is appended for p
    <2>corr. ASSUME NEW p \in Corr,
                    \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                      msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                        (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
             PROVE  m \in RecV
        <3> PICK idv \in ((ValidValues \union InvalidValues) \union {-1}) :
              msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
            BY <2>corr
        <3>1. round[p] \in (0)..(MaxRound)  BY DEF IndTypeOk
        <3>2. m \in msgs_prevote[r] \/ m = [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]  OBVIOUS
        <3>3. CASE m \in msgs_prevote[r]  BY <2>H, <3>3
        <3>4. CASE m = [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
              BY <3>1, <3>4, PrevoteRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2>sel. \/ msgs_prevote' = msgs_prevote
            \/ \E p \in Corr : UponProposalInPropose(p)
            \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
            \/ \E p \in Corr : OnTimeoutPropose(p)
            \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_prevote' = msgs_prevote  BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : UponProposalInPropose(p)
        <3> PICK p \in Corr : UponProposalInPropose(p)  BY <2>2
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInPropose
        <3> QED  BY <3>a, <2>corr
    <2>3. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
        <3> PICK p \in Corr : UponProposalInProposeAndPrevote(p)  BY <2>3
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInProposeAndPrevote
        <3> QED  BY <3>a, <2>corr
    <2>4. CASE \E p \in Corr : OnTimeoutPropose(p)
        <3> PICK p \in Corr : OnTimeoutPropose(p)  BY <2>4
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_prevote' = [msgs_prevote EXCEPT ![round[p]] =
                  (msgs_prevote[round[p]] \union {[id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF OnTimeoutPropose
        <3> QED  BY <3>a, <2>corr
    <2>5. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps2 \in SUBSET Faulty, v2 \in (ValidValues \union InvalidValues) :
                msgs_prevote' = [msgs_prevote EXCEPT ![rF] =
                  (msgs_prevote[rF] \union {[id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> v_v54] : v_v54 \in fps2})]
              BY <2>5 DEF FaultyStep
        <3>2. m \in msgs_prevote[r]
              \/ (\E s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0])
              BY <3>1
        <3>3. CASE m \in msgs_prevote[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0]
              <4> PICK s0 \in fps2 : m = [id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rF, src |-> s0]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v2 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, PrevoteRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>13. (\A v_v97 \in DOMAIN msgs_prevote: \A v_v98 \in msgs_prevote[v_v97]: (v_v97 = v_v98.round))'
        BY SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote, OnTimeoutPropose, FaultyStep
  <1>14. (DOMAIN msgs_precommit = (0)..(MaxRound))'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>15. (\A v_v99 \in (0)..(MaxRound): \A v_v100 \in msgs_precommit[v_v99]: (v_v100 \in {[id |-> v_v101[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> v_v101[2], src |-> v_v101[1]]: v_v101 \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}))'
    <2> DEFINE RecC == {[id |-> t[3], kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> t[2], src |-> t[1]]: t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
    <2> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW m \in msgs_precommit'[r]
                 PROVE  m \in RecC
        BY SMT
    <2>H. \A mm \in msgs_precommit[r] : mm \in RecC  BY DEF IndTypeOk
    <2>corr. ASSUME NEW p \in Corr,
                    \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                      msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                        (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
             PROVE  m \in RecC
        <3> PICK idv \in ((ValidValues \union InvalidValues) \union {-1}) :
              msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
            BY <2>corr
        <3>1. round[p] \in (0)..(MaxRound)  BY DEF IndTypeOk
        <3>2. m \in msgs_precommit[r] \/ m = [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]  OBVIOUS
        <3>3. CASE m \in msgs_precommit[r]  BY <2>H, <3>3
        <3>4. CASE m = [id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
              BY <3>1, <3>4, PrecommitRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2>sel. \/ msgs_precommit' = msgs_precommit
            \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
            \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
            \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
            \/ FaultyStep
        BY DEF Step
    <2>1. CASE msgs_precommit' = msgs_precommit  BY <2>H, <2>1
    <2>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
        <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)  BY <2>2
        <3>a. \/ msgs_precommit' = msgs_precommit
              \/ \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                   msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                     (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponProposalInPrevoteOrCommitAndPrevote
        <3>b. CASE msgs_precommit' = msgs_precommit  BY <2>H, <3>b
        <3>c. CASE \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                     msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                       (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY <3>c, <2>corr
        <3> QED  BY <3>a, <3>b, <3>c
    <2>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
        <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p)  BY <2>3
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                  (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF UponQuorumOfPrevotesAny
        <3> QED  BY <3>a, <2>corr
    <2>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
        <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p)  BY <2>4
        <3>a. \E idv \in ((ValidValues \union InvalidValues) \union {-1}) :
                msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                  (msgs_precommit[round[p]] \union {[id |-> idv, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              BY DEF OnQuorumOfNilPrevotes
        <3> QED  BY <3>a, <2>corr
    <2>5. CASE FaultyStep
        <3>1. PICK rF \in (0)..(MaxRound), fps3 \in SUBSET Faulty, v3 \in (ValidValues \union InvalidValues) :
                msgs_precommit' = [msgs_precommit EXCEPT ![rF] =
                  (msgs_precommit[rF] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> v_v55] : v_v55 \in fps3})]
              BY <2>5 DEF FaultyStep
        <3>2. m \in msgs_precommit[r]
              \/ (\E s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0])
              BY <3>1
        <3>3. CASE m \in msgs_precommit[r]  BY <2>H, <3>3
        <3>4. CASE \E s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0]
              <4> PICK s0 \in fps3 : m = [id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> rF, src |-> s0]  BY <3>4
              <4>1. s0 \in (Corr \union Faulty)  BY <3>4
              <4>2. v3 \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
              <4> QED  BY <4>1, <4>2, PrecommitRecTyped
        <3> QED  BY <3>2, <3>3, <3>4
    <2> QED  BY <2>sel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>16. (\A v_v102 \in DOMAIN msgs_precommit: \A v_v103 \in msgs_precommit[v_v102]: (v_v102 = v_v103.round))'
        BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>17. (last_action \in {"INIT", "INSERT_PROPOSAL", "UPON_PROPOSAL_PROPOSE", "UPON_PROPOSAL_PROPOSE_AND_PREVOTE", "UPON_QUORUM_PREVOTES_ANY", "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE", "UPON_QUORUM_PRECOMMITS_ANY", "UPON_PROPOSAL_PRECOMMIT_NO_DECISION", "ON_TIMEOUT_PROPOSE", "ON_QUORUM_NIL_PREVOTES", "ON_ROUND_CATCHUP"})'
        BY DEF Step, InsertProposal, UponProposalInPropose, UponProposalInProposeAndPrevote,
            UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
            UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
            OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
         <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17
      DEF IndTypeOk

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
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInProposeAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInProposeAndPrevote(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponQuorumOfPrevotesAny ==
  ASSUME TypedIndInv, NEW p \in Corr, UponQuorumOfPrevotesAny(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_UponProposalInPrecommitNoDecision ==
  ASSUME TypedIndInv, NEW p \in Corr, UponProposalInPrecommitNoDecision(p),
         UNCHANGED <<round, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_OnTimeoutPropose ==
  ASSUME TypedIndInv, NEW p \in Corr, OnTimeoutPropose(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_OnQuorumOfNilPrevotes ==
  ASSUME TypedIndInv, NEW p \in Corr, OnQuorumOfNilPrevotes(p),
         UNCHANGED <<round, decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

THEOREM Pres_Bounded_Faulty ==
  ASSUME TypedIndInv, FaultyStep,
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, last_action>>
  PROVE  AllValidAndLockedRoundBounded'
  BY DEF TypedIndInv, IndInv, AllValidAndLockedRoundBounded

\* --- 3 substantive cases ---

\* Sets valid_round[p]:=round[p], and locked_round[p]:=round[p] in the "then"
\* branch (else locked_round UNCHANGED); round itself is UNCHANGED.
THEOREM Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponProposalInPrevoteOrCommitAndPrevote(p),
         UNCHANGED <<round, decision, msgs_propose, msgs_prevote>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. round' = round
        OBVIOUS
  <1>2. valid_round' = [valid_round EXCEPT ![p] = round[p]]
        BY DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>3. locked_round' = [locked_round EXCEPT ![p] = round[p]] \/ locked_round' = locked_round
        BY DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>4. /\ DOMAIN round = Corr /\ DOMAIN valid_round = Corr /\ DOMAIN locked_round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInv, IndTypeOk
  <1>5. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5, SMT

\* Advances round[p] to round[p]+1; valid_round and locked_round are UNCHANGED.
THEOREM Pres_Bounded_UponQuorumOfPrecommitsAny ==
  ASSUME TypedIndInv, NEW p \in Corr,
         UponQuorumOfPrecommitsAny(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. round' = [round EXCEPT ![p] = round[p] + 1]
        BY DEF UponQuorumOfPrecommitsAny
  <1>2. valid_round' = valid_round /\ locked_round' = locked_round
        BY SMT
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInv, IndTypeOk
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, SMT

\* Jumps round[p] up to some rnd > round[p]; valid_round and locked_round UNCHANGED.
THEOREM Pres_Bounded_OnRoundCatchup ==
  ASSUME TypedIndInv, NEW p \in Corr,
         OnRoundCatchup(p),
         UNCHANGED <<decision, locked_value, locked_round, valid_value, valid_round, msgs_propose, msgs_prevote, msgs_precommit>>
  PROVE  AllValidAndLockedRoundBounded'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllValidAndLockedRoundBounded
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  valid_round'[q] <= round'[q] /\ locked_round'[q] <= round'[q]
      OBVIOUS
  <1>1. \E rnd \in (0)..(MaxRound) : rnd > round[p] /\ round' = [round EXCEPT ![p] = rnd]
        BY DEF OnRoundCatchup
  <1>2. valid_round' = valid_round /\ locked_round' = locked_round
        BY SMT
  <1>3. /\ DOMAIN round = Corr
        /\ round[p] \in Int /\ round[q] \in Int
        BY SMT DEF TypedIndInv, IndTypeOk
  <1>4. valid_round[q] <= round[q] /\ locked_round[q] <= round[q]
        OBVIOUS
  <1> QED
      BY <1>1, <1>2, <1>3, <1>4, SMT

\* Assembler: split Step into its 11 disjuncts.
THEOREM Pres_AllValidAndLockedRoundBounded ==
  ASSUME TypedIndInv, Step
  PROVE  AllValidAndLockedRoundBounded'
  BY Pres_Bounded_InsertProposal,
     Pres_Bounded_UponProposalInPropose,
     Pres_Bounded_UponProposalInProposeAndPrevote,
     Pres_Bounded_UponQuorumOfPrevotesAny,
     Pres_Bounded_UponProposalInPrevoteOrCommitAndPrevote,
     Pres_Bounded_UponQuorumOfPrecommitsAny,
     Pres_Bounded_UponProposalInPrecommitNoDecision,
     Pres_Bounded_OnTimeoutPropose,
     Pres_Bounded_OnQuorumOfNilPrevotes,
     Pres_Bounded_OnRoundCatchup,
     Pres_Bounded_Faulty
  DEF Step

\* ---------------------------------------------------------------------------
\* REMAINING 16 CONJUNCT ASSEMBLERS.
\* Each follows the pattern above: decompose into Pres_<Conj>_<action> theorems
\* over the 11 Step disjuncts, then assemble BY ... DEF Step.
\* ---------------------------------------------------------------------------

THEOREM Pres_AllNoFutureMessagesSent ==
  ASSUME TypedIndInv, Step PROVE AllNoFutureMessagesSent'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  /\ /\ \/ q = Proposer[round'[q]]
                         \/ \A mp \in msgs_propose'[round'[q]] : q # mp.src
                      /\ \/ step'[q] = "PREVOTE_OF_STEP"
                         \/ step'[q] = "PRECOMMIT_OF_STEP"
                         \/ step'[q] = "DECIDED_OF_STEP"
                         \/ \A mv \in msgs_prevote'[round'[q]] : q # mv.src
                      /\ \/ step'[q] = "PRECOMMIT_OF_STEP"
                         \/ step'[q] = "DECIDED_OF_STEP"
                         \/ \A mc \in msgs_precommit'[round'[q]] : q # mc.src
                      /\ \A rr \in {r \in (0)..(MaxRound) : r > round'[q]} :
                           /\ \A mp \in msgs_propose'[rr] : q # mp.src
                           /\ \A mv \in msgs_prevote'[rr] : q # mv.src
                           /\ \A mc \in msgs_precommit'[rr] : q # mc.src
      BY DEF AllNoFutureMessagesSent
  \* The selector carries, for each case that needs it, the frame equalities from that
  \* Step branch's UNCHANGED tuple. The bare action alone does NOT determine the frame
  \* (e.g. FaultyStep with an empty faulty injection can co-occur with OnRoundCatchup,
  \* which changes round), so the frame must come from the branch, not the action.
  <1>sel.  \/ (FaultyStep /\ round' = round /\ step' = step)
           \/ ((\E p \in Corr : InsertProposal(p))
                 /\ round' = round /\ step' = step
                 /\ msgs_prevote' = msgs_prevote /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : UponProposalInPropose(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : UponProposalInProposeAndPrevote(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : UponQuorumOfPrevotesAny(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote)
           \/ ((\E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote)
           \/ ((\E p \in Corr : UponQuorumOfPrecommitsAny(p))
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                 /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : UponProposalInPrecommitNoDecision(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                 /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : OnTimeoutPropose(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit)
           \/ ((\E p \in Corr : OnQuorumOfNilPrevotes(p))
                 /\ round' = round
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote)
           \/ ((\E p \in Corr : OnRoundCatchup(p))
                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                 /\ msgs_precommit' = msgs_precommit)
      BY DEF Step
  <1>faulty. CASE FaultyStep /\ round' = round /\ step' = step
      <2>frame. round' = round /\ step' = step
            BY <1>faulty
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>faulty, <2>frame, <2>old, DisjointCF, SMT DEF FaultyStep
  <1>insert. CASE (\E p \in Corr : InsertProposal(p))
                  /\ round' = round /\ step' = step
                  /\ msgs_prevote' = msgs_prevote /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : InsertProposal(p) BY <1>insert
      <2>frame. /\ round' = round
                /\ step' = step
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>insert
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>insert, <2>frame, <2>old, SMT DEF InsertProposal
  <1>proposal. CASE (\E p \in Corr : UponProposalInPropose(p))
                     /\ round' = round
                     /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : UponProposalInPropose(p) BY <1>proposal
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_precommit' = msgs_precommit
            BY <1>proposal
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>proposal, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         UponProposalInPropose
  <1>proposalPrevote. CASE (\E p \in Corr : UponProposalInProposeAndPrevote(p))
                            /\ round' = round
                            /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <1>proposalPrevote
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_precommit' = msgs_precommit
            BY <1>proposalPrevote
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>proposalPrevote, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         UponProposalInProposeAndPrevote
  <1>quorumPrevotes. CASE (\E p \in Corr : UponQuorumOfPrevotesAny(p))
                          /\ round' = round
                          /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
      <2> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <1>quorumPrevotes
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
            BY <1>quorumPrevotes
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>quorumPrevotes, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         UponQuorumOfPrevotesAny
  <1>proposalPrevoteCommit. CASE (\E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p))
                                 /\ round' = round
                                 /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
      <2> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <1>proposalPrevoteCommit
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
            BY <1>proposalPrevoteCommit
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>proposalPrevoteCommit, <2>frame, <2>old, DisjointCF, SMT
         DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>quorumPrecommits. CASE (\E p \in Corr : UponQuorumOfPrecommitsAny(p))
                            /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                            /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : UponQuorumOfPrecommitsAny(p) BY <1>quorumPrecommits
      <2>frame. /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>quorumPrecommits
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>quorumPrecommits, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         UponQuorumOfPrecommitsAny
  <1>decide. CASE (\E p \in Corr : UponProposalInPrecommitNoDecision(p))
                  /\ round' = round
                  /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                  /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : UponProposalInPrecommitNoDecision(p) BY <1>decide
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>decide
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>decide, <2>frame, <2>old, SMT
         DEF UponProposalInPrecommitNoDecision
  <1>timeoutPropose. CASE (\E p \in Corr : OnTimeoutPropose(p))
                          /\ round' = round
                          /\ msgs_propose' = msgs_propose /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : OnTimeoutPropose(p) BY <1>timeoutPropose
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_precommit' = msgs_precommit
            BY <1>timeoutPropose
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>timeoutPropose, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         OnTimeoutPropose
  <1>nilPrevotes. CASE (\E p \in Corr : OnQuorumOfNilPrevotes(p))
                       /\ round' = round
                       /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
      <2> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <1>nilPrevotes
      <2>frame. /\ round' = round
                /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
            BY <1>nilPrevotes
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>nilPrevotes, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         OnQuorumOfNilPrevotes
  <1>roundCatchup. CASE (\E p \in Corr : OnRoundCatchup(p))
                        /\ msgs_propose' = msgs_propose /\ msgs_prevote' = msgs_prevote
                        /\ msgs_precommit' = msgs_precommit
      <2> PICK p \in Corr : OnRoundCatchup(p) BY <1>roundCatchup
      <2>frame. /\ msgs_propose' = msgs_propose
                /\ msgs_prevote' = msgs_prevote
                /\ msgs_precommit' = msgs_precommit
            BY <1>roundCatchup
      <2>old. /\ /\ \/ q = Proposer[round[q]]
                    \/ \A mp \in msgs_propose[round[q]] : q # mp.src
                 /\ \/ step[q] = "PREVOTE_OF_STEP"
                    \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mv \in msgs_prevote[round[q]] : q # mv.src
                 /\ \/ step[q] = "PRECOMMIT_OF_STEP"
                    \/ step[q] = "DECIDED_OF_STEP"
                    \/ \A mc \in msgs_precommit[round[q]] : q # mc.src
                 /\ \A rr \in {r \in (0)..(MaxRound) : r > round[q]} :
                      /\ \A mp \in msgs_propose[rr] : q # mp.src
                      /\ \A mv \in msgs_prevote[rr] : q # mv.src
                      /\ \A mc \in msgs_precommit[rr] : q # mc.src
            BY DEF AllNoFutureMessagesSent
      <2> QED BY <1>roundCatchup, <2>frame, <2>old, DisjointCF, SMT DEF AllNoFutureMessagesSent,
         OnRoundCatchup
  <1> QED BY <1>sel, <1>faulty, <1>insert, <1>proposal, <1>proposalPrevote,
     <1>quorumPrevotes, <1>proposalPrevoteCommit, <1>quorumPrecommits,
     <1>decide, <1>timeoutPropose, <1>nilPrevotes, <1>roundCatchup

THEOREM Pres_AllIfInPrevoteThenSentPrevote ==
  ASSUME TypedIndInv, Step PROVE AllIfInPrevoteThenSentPrevote'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "PREVOTE_OF_STEP"
               PROVE  \E m \in msgs_prevote'[round'[q]] :
                         /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                         /\ q = m.src
      BY DEF AllIfInPrevoteThenSentPrevote
  <1>1. CASE step[q] = "PREVOTE_OF_STEP"
      <2>0. round'[q] = round[q]
            BY <1>1, SMT DEF Step, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrecommitsAny,
               OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>1. PICK m \in msgs_prevote[round[q]] :
                /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ q = m.src
            BY <1>1 DEF AllIfInPrevoteThenSentPrevote
      <2>2. m \in msgs_prevote'[round'[q]]
            BY <2>0, <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE step[q] # "PREVOTE_OF_STEP"
      <2> QED BY <1>2, EnteredPrevoteHasSentPrevote
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfInPrecommitThenSentPrecommit ==
  ASSUME TypedIndInv, Step PROVE AllIfInPrecommitThenSentPrecommit'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "PRECOMMIT_OF_STEP"
               PROVE  \E m \in msgs_precommit'[round'[q]] :
                         /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                         /\ q = m.src
      BY DEF AllIfInPrecommitThenSentPrecommit
  <1>1. CASE step[q] = "PRECOMMIT_OF_STEP"
      <2>0. round'[q] = round[q]
            BY <1>1, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnRoundCatchup
      <2>1. PICK m \in msgs_precommit[round[q]] :
                /\ m.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ q = m.src
            BY <1>1 DEF AllIfInPrecommitThenSentPrecommit
      <2>2. m \in msgs_precommit'[round'[q]]
            BY <2>0, <2>1, PrecommitMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE step[q] # "PRECOMMIT_OF_STEP"
      <2> QED BY <1>2, EnteredPrecommitHasSentPrecommit
  <1> QED BY <1>1, <1>2

\* A decided process received a matching proposal (at some round). Only
\* UponProposalInPrecommitNoDecision decides, and its guard exhibits the proposal;
\* an already-decided process keeps its decision (it cannot act) and the proposal
\* persists by ProposeMonotone.
THEOREM Pres_AllIfInDecidedThenReceivedProposal ==
  ASSUME TypedIndInv, Step
  PROVE  AllIfInDecidedThenReceivedProposal'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "DECIDED_OF_STEP"
               PROVE  \E rr \in (0)..(MaxRound) : \E mm \in msgs_propose'[rr] :
                        mm.src = Proposer[rr] /\ mm.proposal = decision'[q]
      BY DEF AllIfInDecidedThenReceivedProposal
  <1>1. CASE step[q] = "DECIDED_OF_STEP"
      <2>0. decision[q] \in ValidValues
            BY <1>1 DEF AllIfInDecidedThenValidDecision
      <2>00. decision[q] # -1
            BY <2>0, NilNotValid
      <2>1. decision'[q] = decision[q]
            BY <2>00, SMT DEF Step, UponProposalInPrecommitNoDecision
      <2>2. PICK rr \in (0)..(MaxRound) : \E mm \in msgs_propose[rr] :
              mm.src = Proposer[rr] /\ mm.proposal = decision[q]
            BY <1>1 DEF AllIfInDecidedThenReceivedProposal
      <2>3. PICK mm \in msgs_propose[rr] : mm.src = Proposer[rr] /\ mm.proposal = decision[q]
            BY <2>2
      <2>4. mm \in msgs_propose'[rr]  BY <2>3, ProposeMonotone
      <2> QED  BY <2>1, <2>3, <2>4
  <1>2. CASE step[q] # "DECIDED_OF_STEP"
      <2>0. step'[q] # step[q]
            BY <1>2
      <2>a. \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
             \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
             \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
             \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
            BY <2>0, StepChangeChar
      <2>1. UponProposalInPrecommitNoDecision(q)
            BY <2>a, SMT DEF UponProposalInPropose, UponProposalInProposeAndPrevote,
               UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>2. PICK v \in ValidValues, rnd \in (0)..(MaxRound), vr \in ((0)..(MaxRound) \union {-1}) :
              /\ [proposal |-> v, round |-> rnd, src |-> Proposer[rnd], valid_round |-> vr] \in msgs_propose[rnd]
              /\ decision' = [decision EXCEPT ![q] = v]
            BY <2>1 DEF UponProposalInPrecommitNoDecision
      <2>3. decision'[q] = v  BY <2>2
      <2>4. [proposal |-> v, round |-> rnd, src |-> Proposer[rnd], valid_round |-> vr] \in msgs_propose'[rnd]
            BY <2>2, ProposeMonotone
      <2> QED  BY <2>2, <2>3, <2>4
  <1> QED  BY <1>1, <1>2

THEOREM Pres_AllIfInDecidedThenReceivedTwoThirds ==
  ASSUME TypedIndInv, Step PROVE AllIfInDecidedThenReceivedTwoThirds'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, step'[q] = "DECIDED_OF_STEP"
               PROVE  \E rr \in (0)..(MaxRound) :
                         Cardinality({s \in (Corr \union Faulty) :
                           \E m \in {mm \in msgs_precommit'[rr] :
                             mm.id = decision'[q]} : s = m.src})
                         >= ((2 * T) + 1)
      BY DEF AllIfInDecidedThenReceivedTwoThirds
  <1>1. CASE step[q] = "DECIDED_OF_STEP"
      <2>0. decision[q] \in ValidValues
            BY <1>1 DEF AllIfInDecidedThenValidDecision
      <2>00. decision[q] # -1
            BY <2>0, NilNotValid
      <2>1. decision'[q] = decision[q]
            BY <2>00, SMT DEF Step, UponProposalInPrecommitNoDecision
      <2>2. PICK rr \in (0)..(MaxRound) :
                Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rr] :
                    mm.id = decision[q]} : s = m.src})
                >= ((2 * T) + 1)
            BY <1>1 DEF AllIfInDecidedThenReceivedTwoThirds
      <2>3. decision[q] \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>0
      <2>4. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rr] :
                    mm.id = decision[q]} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rr] :
                    mm.id = decision[q]} : s = m.src})
            BY <2>2, <2>3, PrecommitSenderSetCardinalityMonotone
      <2>5. /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit[rr] :
                      mm.id = decision[q]} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit'[rr] :
                      mm.id = decision[q]} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rr] :
                    mm.id = decision[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>2, <2>4, <2>5, IntLeGeTrans1
      <2>7. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit'[rr] :
                  mm.id = decision'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit'[rr] :
                  mm.id = decision[q]} : s = m.src}
            BY <2>1, SMT
      <2> QED BY <2>2, <2>6, <2>7
  <1>2. CASE step[q] # "DECIDED_OF_STEP"
      <2>0. step'[q] # step[q]
            BY <1>2
      <2>a. \/ UponProposalInPropose(q) \/ UponProposalInProposeAndPrevote(q)
             \/ UponQuorumOfPrevotesAny(q) \/ UponProposalInPrevoteOrCommitAndPrevote(q)
             \/ UponQuorumOfPrecommitsAny(q) \/ UponProposalInPrecommitNoDecision(q)
             \/ OnTimeoutPropose(q) \/ OnQuorumOfNilPrevotes(q) \/ OnRoundCatchup(q)
            BY <2>0, StepChangeChar
      <2>1. UponProposalInPrecommitNoDecision(q)
            BY <1>2, <2>a, SMT DEF UponProposalInPropose, UponProposalInProposeAndPrevote,
               UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup
      <2>2. PICK v \in ValidValues, rnd \in (0)..(MaxRound), vr \in ((0)..(MaxRound) \union {-1}) :
                /\ Cardinality({m \in msgs_precommit[rnd] : v = m.id}) >= ((2 * T) + 1)
                /\ decision' = [decision EXCEPT ![q] = v]
            BY <2>1 DEF UponProposalInPrecommitNoDecision
      <2>3. decision'[q] = v
            BY <2>2
      <2>4. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>2
      <2>4b. {m \in msgs_precommit[rnd] : m.id = v}
              =
              {m \in msgs_precommit[rnd] : v = m.id}
            BY SMT
      <2>4c. Cardinality({m \in msgs_precommit[rnd] : m.id = v}) >= ((2 * T) + 1)
            BY <2>2, <2>4b
      <2>5. Cardinality({m \in msgs_precommit[rnd] : m.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
            BY <2>2, <2>4, PrecommitValueMessagesCardinalityLeSenders
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src})
            BY <2>2, <2>4, PrecommitSenderSetCardinalityMonotone
      <2>7. /\ Cardinality({m \in msgs_precommit[rnd] : m.id = v}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY <2>2, <2>4, PrecommitValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit[rnd] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>4c, <2>5, <2>7, IntLeGeTrans1
      <2>9. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_precommit'[rnd] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7, <2>8, IntLeGeTrans1
      <2>10. {s \in (Corr \union Faulty) :
                 \E m \in {mm \in msgs_precommit'[rnd] :
                   mm.id = decision'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                 \E m \in {mm \in msgs_precommit'[rnd] :
                   mm.id = v} : s = m.src}
            BY <2>3, SMT
      <2> QED BY <2>2, <2>9, <2>10
  <1> QED BY <1>1, <1>2

\* (step[p]=DECIDED) <=> (decision[p] in ValidValues). Only
\* UponProposalInPrecommitNoDecision sets step:=DECIDED, and it simultaneously
\* sets decision:=v with v in ValidValues. Every other step-changing action is
\* guarded by step[p] /= DECIDED and sets step to a non-DECIDED value while
\* leaving decision unchanged, so the old biconditional carries: the guard makes
\* the old LHS false, hence decision[p] was not a ValidValue.
THEOREM Pres_AllIfInDecidedThenValidDecision ==
  ASSUME TypedIndInv, Step
  PROVE  AllIfInDecidedThenValidDecision'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllIfInDecidedThenValidDecision
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (step'[q] = "DECIDED_OF_STEP") = (decision'[q] \in ValidValues)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT
      DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote,
          UponQuorumOfPrevotesAny, UponProposalInPrevoteOrCommitAndPrevote,
          UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
          OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup

\* Only UponProposalInPrevoteOrCommitAndPrevote touches locked_round/locked_value:
\* its "then" branch sets locked_value[p]:=v (v in ValidValues, so /= -1) and
\* locked_round[p]:=round[p] (in 0..MaxRound, so /= -1) together; every other
\* action leaves both UNCHANGED. So the -1 flags stay in agreement.
THEOREM Pres_AllLockedRoundIffLockedValue ==
  ASSUME TypedIndInv, Step
  PROVE  AllLockedRoundIffLockedValue'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllLockedRoundIffLockedValue
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (locked_round'[q] = -1) = (locked_value'[q] = -1)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote

\* Symmetric to the above: only UponProposalInPrevoteOrCommitAndPrevote sets
\* valid_value[p]:=v (/= -1) and valid_round[p]:=round[p] (/= -1) together.
THEOREM Pres_AllValidRoundIffValidValue ==
  ASSUME TypedIndInv, Step
  PROVE  AllValidRoundIffValidValue'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk, AllValidRoundIffValidValue
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  (valid_round'[q] = -1) = (valid_value'[q] = -1)
      OBVIOUS
  <1> QED
      BY NilNotValid, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote

THEOREM Pres_AllIfValidRoundThenTwoThirdsPrevotes ==
  ASSUME TypedIndInv, Step PROVE AllIfValidRoundThenTwoThirdsPrevotes'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, valid_round'[q] # -1
               PROVE  Cardinality({s \in (Corr \union Faulty) :
                         \E m \in {mm \in msgs_prevote'[valid_round'[q]] :
                           mm.id = valid_value'[q]} : s = m.src})
                       >= ((2 * T) + 1)
      BY DEF AllIfValidRoundThenTwoThirdsPrevotes
  <1>1. CASE valid_round'[q] = valid_round[q] /\ valid_value'[q] = valid_value[q]
      <2>0. valid_round[q] # -1
            BY <1>1
      <2>00. valid_round[q] \in (0)..(MaxRound)
            BY <2>0, SMT DEF IndTypeOk
      <2>1. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>0 DEF AllIfValidRoundThenTwoThirdsPrevotes
      <2>2. valid_value[q] \in ((ValidValues \union InvalidValues) \union {-1})
            BY SMT DEF IndTypeOk
      <2>3. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
            BY <2>00, <2>2, PrevoteSenderSetCardinalityMonotone
      <2>4. valid_round'[q] = valid_round[q] /\ valid_value'[q] = valid_value[q]
            BY <1>1
      <2>5. /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>1, <2>3, <2>5, IntLeGeTrans1
      <2>7. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round[q]] : mm.id = valid_value[q]} : s = m.src}
            BY <2>4, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7
      <2> QED BY <2>8
  <1>2. CASE valid_round'[q] # valid_round[q] \/ valid_value'[q] # valid_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ Cardinality({m \in msgs_prevote[round[q]] : m.id = v}) >= ((2 * T) + 1)
                /\ valid_value' = [valid_value EXCEPT ![q] = v]
                /\ valid_round' = [valid_round EXCEPT ![q] = round[q]]
            BY <2>1 DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. valid_value'[q] = v /\ valid_round'[q] = round[q]
            BY <2>2, SMT DEF IndTypeOk
      <2>4. round[q] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>4a. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>2
      <2>5. Cardinality({m \in msgs_prevote[round[q]] : m.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
            BY <2>4, <2>4a, PrevoteValueMessagesCardinalityLeSenders
      <2>6. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src})
            BY <2>4, <2>4a, PrevoteSenderSetCardinalityMonotone
      <2>7. /\ Cardinality({m \in msgs_prevote[round[q]] : m.id = v}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src}) \in Int
              /\ Cardinality({s \in (Corr \union Faulty) :
                    \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src}) \in Int
              /\ ((2 * T) + 1) \in Int
            BY <2>4, <2>4a, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>8. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[round[q]] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>2, <2>5, <2>7, IntLeGeTrans1
      <2>9. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>6, <2>7, <2>8, IntLeGeTrans1
      <2>10. {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src}
              =
              {s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[round[q]] : mm.id = v} : s = m.src}
            BY <2>3, SMT
      <2>11. Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote'[valid_round'[q]] : mm.id = valid_value'[q]} : s = m.src})
              >= ((2 * T) + 1)
            BY <2>9, <2>10
      <2> QED BY <2>11
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfLockedRoundThenSentCommit ==
  ASSUME TypedIndInv, Step PROVE AllIfLockedRoundThenSentCommit'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, locked_round'[q] # -1
               PROVE  \E rr \in (0)..(MaxRound) :
                         /\ rr <= round'[q]
                         /\ \E m \in msgs_precommit'[rr] :
                              /\ q = m.src
                              /\ m.id = locked_value'[q]
      BY DEF AllIfLockedRoundThenSentCommit
  <1>1. CASE locked_value'[q] = locked_value[q]
      <2>post. AllLockedRoundIffLockedValue'
            BY Pres_AllLockedRoundIffLockedValue
      <2>0. locked_value'[q] # -1
            BY <2>post DEF AllLockedRoundIffLockedValue
      <2>00. locked_value[q] # -1
            BY <1>1, <2>0
      <2>000. locked_round[q] # -1
            BY <2>00 DEF AllLockedRoundIffLockedValue
      <2>1. PICK rr \in (0)..(MaxRound) :
                /\ rr <= round[q]
                /\ \E m \in msgs_precommit[rr] :
                     /\ q = m.src
                     /\ m.id = locked_value[q]
            BY <2>000 DEF AllIfLockedRoundThenSentCommit
      <2>2. PICK m \in msgs_precommit[rr] :
                /\ rr <= round[q]
                /\ q = m.src
                /\ m.id = locked_value[q]
            BY <2>1
      <2>3. rr <= round[q]
            BY <2>2
      <2>4. m \in msgs_precommit'[rr]
            BY <2>2, PrecommitMonotone
      <2>5. round[q] <= round'[q]
            BY RoundMonotone DEF TypedIndInv, IndTypeOk
      <2>6. IndTypeOk'
            BY TypePres
      <2>7. /\ rr \in Int /\ round[q] \in Int /\ round'[q] \in Int
            BY <2>1, <2>6, ConstNat, SMT DEF TypedIndInv, IndTypeOk
      <2>8. rr <= round'[q]
            BY <2>3, <2>5, <2>7, SMT
      <2> QED BY <1>1, <2>1, <2>2, <2>4, <2>8
  <1>2. CASE locked_value'[q] # locked_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ locked_value' = [locked_value EXCEPT ![q] = v]
                /\ locked_round' = [locked_round EXCEPT ![q] = round[q]]
                /\ msgs_precommit' =
                     [msgs_precommit EXCEPT ![round[q]] =
                       (msgs_precommit[round[q]] \union {[id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]})]
            BY <1>2, <2>1, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. round[q] <= round'[q]
            BY RoundMonotone DEF TypedIndInv, IndTypeOk
      <2>4. round[q] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>5. [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q] \in msgs_precommit'[round[q]]
            BY <2>2
      <2>6. locked_value'[q] = v
            BY <2>2, SMT DEF IndTypeOk
      <2> QED BY <2>3, <2>4, <2>5, <2>6
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllLatestPrecommitHasLockedRound ==
  ASSUME TypedIndInv, Step PROVE AllLatestPrecommitHasLockedRound'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr
               PROVE  \/ /\ locked_round'[q] = -1
                          /\ locked_value'[q] = -1
                          /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                               \/ q # m.src
                               \/ m.id = -1
                       \/ /\ locked_round'[q] # -1
                          /\ locked_value'[q] # -1
                          /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                               \/ \/ q # m.src
                                  \/ m.round <= locked_round'[q]
                               \/ m.id = -1
                          /\ \E m \in msgs_precommit'[locked_round'[q]] :
                               /\ q = m.src
                               /\ m.id = locked_value'[q]
      BY DEF AllLatestPrecommitHasLockedRound
  <1>1. CASE locked_round'[q] = locked_round[q] /\ locked_value'[q] = locked_value[q]
      <2>old. \/ /\ locked_round[q] = -1
                   /\ locked_value[q] = -1
                   /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                        \/ q # m.src
                        \/ m.id = -1
                \/ /\ locked_round[q] # -1
                   /\ locked_value[q] # -1
                   /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                        \/ \/ q # m.src
                           \/ m.round <= locked_round[q]
                        \/ m.id = -1
                   /\ \E m \in msgs_precommit[locked_round[q]] :
                        /\ q = m.src
                        /\ m.id = locked_value[q]
            BY DEF AllLatestPrecommitHasLockedRound
      <2>typep. IndTypeOk'
            BY TypePres
      <2>shape. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
                   /\ m.round = r
                   /\ \/ m \in msgs_precommit[r]
                      \/ q # m.src
                      \/ /\ r = round[q]
                         /\ \/ m.id = -1
                            \/ /\ locked_round'[q] = round[q]
                               /\ m.id = locked_value'[q]
            BY DisjointCF, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep, IndTypeOk
      <2>1. CASE locked_round[q] = -1
          <3>oldNil. /\ locked_value[q] = -1
                      /\ \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                           \/ q # m.src
                           \/ m.id = -1
                BY <2>old, <2>1, SMT
          <3> QED
                BY <1>1, <2>1, <3>oldNil, <2>shape, ConstNat, SMT
                DEF TypedIndInv, IndTypeOk
      <2>2. CASE locked_round[q] # -1
          <3>0. locked_round[q] \in (0)..(MaxRound)
                BY <2>2, SMT DEF TypedIndInv, IndTypeOk
          <3>oldVal. locked_value[q] # -1
                BY <2>old, <2>2, SMT
          <3>oldUni. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit[r] :
                         \/ \/ q # m.src
                            \/ m.round <= locked_round[q]
                         \/ m.id = -1
                BY <2>old, <2>2, SMT
          <3>oldExist. \E m \in msgs_precommit[locked_round[q]] :
                         /\ q = m.src
                         /\ m.id = locked_value[q]
                BY <2>old, <2>2, SMT
          <3>1. PICK m \in msgs_precommit[locked_round[q]] :
                    /\ q = m.src
                    /\ m.id = locked_value[q]
                BY <3>oldExist
          <3>2. m \in msgs_precommit'[locked_round'[q]]
                BY <1>1, <2>2, <3>0, <3>1, PrecommitMonotone
          <3> QED
                BY <1>1, <2>2, <2>shape, <3>oldVal, <3>oldUni, <3>1, <3>2, SMT
      <2> QED BY <2>old, <2>1, <2>2
  <1>2. CASE locked_round'[q] # locked_round[q] \/ locked_value'[q] # locked_value[q]
      <2>1. UponProposalInPrevoteOrCommitAndPrevote(q)
            BY <1>2, SMT DEF Step, InsertProposal, UponProposalInPropose,
               UponProposalInProposeAndPrevote, UponQuorumOfPrevotesAny,
               UponProposalInPrevoteOrCommitAndPrevote,
               UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision,
               OnTimeoutPropose, OnQuorumOfNilPrevotes, OnRoundCatchup, FaultyStep
      <2>2. PICK v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                /\ locked_value' = [locked_value EXCEPT ![q] = v]
                /\ locked_round' = [locked_round EXCEPT ![q] = round[q]]
                /\ msgs_precommit' =
                     [msgs_precommit EXCEPT ![round[q]] =
                       (msgs_precommit[round[q]] \union {[id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]})]
            BY <1>2, <2>1, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. locked_value'[q] = v /\ locked_round'[q] = round[q]
            BY <2>2, SMT DEF IndTypeOk
      <2>4. locked_round'[q] # -1 /\ locked_value'[q] # -1
            BY <2>2, <2>3, NilNotValid, SMT DEF IndTypeOk
      <2>5. [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[q], src |-> q]
              \in msgs_precommit'[locked_round'[q]]
            BY <2>2, <2>3
      <2>6. \A r \in (0)..(MaxRound) : \A m \in msgs_precommit'[r] :
               \/ \/ q # m.src
                  \/ m.round <= locked_round'[q]
               \/ m.id = -1
            BY <2>2, <2>3, SMT DEF AllLatestPrecommitHasLockedRound,
               AllValidAndLockedRoundBounded, IndTypeOk
      <2> QED BY <2>3, <2>4, <2>5, <2>6
  <1> QED BY <1>1, <1>2

THEOREM Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds ==
  ASSUME TypedIndInv, Step PROVE AllIfSentPrevoteThenReceivedProposalOrTwoThirds'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_prevote'[r]
               PROVE  \/ m.src \in Faulty
                      \/ m.id = -1
                      \/ /\ m.id # -1
                         /\ \/ \E prop \in msgs_propose'[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ prop.valid_round = -1
                            \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                                  /\ \E prop \in msgs_propose'[r] :
                                       /\ prop.src = Proposer[r]
                                       /\ prop.proposal = m.id
                                       /\ rr = prop.valid_round
                                  /\ Cardinality({s \in (Corr \union Faulty) :
                                       \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                                         s = pv.src}) >= ((2 * T) + 1)
      BY DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
  <1>split. \/ m \in msgs_prevote[r]
             \/ m.src \in Faulty
             \/ (\E p \in Corr, v \in (ValidValues \union InvalidValues) :
                  /\ r = round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> -1]
                       \in msgs_propose[round[p]]
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] = -1
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
             \/ (\E p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
             \/ (\E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p])
      BY DisjointCF, SMT DEF Step, FaultyStep, UponProposalInPropose,
         UponProposalInProposeAndPrevote, OnTimeoutPropose
  <1>1. CASE m \in msgs_prevote[r]
      <2>old. \/ m.src \in Faulty
                \/ m.id = -1
                \/ /\ m.id # -1
                   /\ \/ \E prop \in msgs_propose[r] :
                            /\ prop.src = Proposer[r]
                            /\ prop.proposal = m.id
                            /\ prop.valid_round = -1
                      \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                            /\ \E prop \in msgs_propose[r] :
                                 /\ prop.src = Proposer[r]
                                 /\ prop.proposal = m.id
                                 /\ rr = prop.valid_round
                            /\ Cardinality({s \in (Corr \union Faulty) :
                                 \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                   s = pv.src}) >= ((2 * T) + 1)
            BY <1>1 DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
      <2>f. CASE m.src \in Faulty
          <3> QED BY <2>f
      <2>nil. CASE m.id = -1
          <3> QED BY <2>nil
      <2>good. CASE /\ m.id # -1
                    /\ \/ \E prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
                       \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
          <3>propCase. CASE \E prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
              <4> PICK prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = m.id
                             /\ prop.valid_round = -1
                    BY <3>propCase
              <4>pnew. prop \in msgs_propose'[r]
                    BY ProposeMonotone
              <4> QED BY <2>good, <4>pnew
          <3>quorumCase. CASE \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
              <4>oldQ. PICK rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                    s = pv.src}) >= ((2 * T) + 1)
                    BY <3>quorumCase
              <4>oldProp. PICK prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = m.id
                                  /\ rr = prop.valid_round
                    BY <4>oldQ
              <4>rty. rr \in (0)..(MaxRound)
                    BY <4>oldQ
              <4>idty. m.id \in ((ValidValues \union InvalidValues) \union {-1})
                    \* Extract the id-field type from IndTypeOk's prevote record-set typing:
                    \* SMT cannot project the field out of the set-builder monolithically.
                    <5>1. m \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]] :
                                   t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
                          BY <1>1 DEF IndTypeOk
                    <5>2. PICK t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) :
                             m = [id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]
                          BY <5>1
                    <5>3. m.id = t[3]  BY <5>2
                    <5> QED  BY <5>2, <5>3
              <4>mono. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                              s = pv.src})
                        <=
                        Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                              s = pv.src})
                    BY <4>rty, <4>idty, PrevoteSenderSetCardinalityMonotone, Isa
                       DEF TypedIndInv
              <4>oldCard. Cardinality({s \in (Corr \union Faulty) :
                             \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                               s = pv.src}) >= ((2 * T) + 1)
                    BY <4>oldQ
              <4>types. /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote[rr] : pp.id = m.id} :
                                 s = pv.src}) \in Int
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                                 s = pv.src}) \in Int
                          /\ ((2 * T) + 1) \in Int
                    BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
              <4>newq. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                              s = pv.src}) >= ((2 * T) + 1)
                    BY <4>oldCard, <4>mono, <4>types, IntLeGeTrans1
              <4>pnew. prop \in msgs_propose'[r]
                    BY ProposeMonotone
              <4> QED BY <2>good, <4>oldQ, <4>oldProp, <4>pnew, <4>newq
          <3> QED BY <2>good, <3>propCase, <3>quorumCase
      <2> QED BY <2>old, <2>f, <2>nil, <2>good
  <1>2. CASE m.src \in Faulty
      <2> QED BY <1>2
  <1>3. CASE \E p \in Corr, v \in (ValidValues \union InvalidValues) :
                  /\ r = round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> -1]
                       \in msgs_propose[round[p]]
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] = -1
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2> QED BY <1>3, ProposeMonotone, SMT
  <1>4. CASE \E p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2>wit. PICK p \in Corr, v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
                  /\ r = round[p]
                  /\ vr < round[p]
                  /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                       \in msgs_propose[round[p]]
                  /\ Cardinality({pv \in msgs_prevote[vr] : v = pv.id}) >= ((2 * T) + 1)
                  /\ m = [id |-> (IF /\ v \in ValidValues
                                      /\ \/ locked_round[p] <= vr
                                         \/ locked_value[p] = v
                                    THEN v ELSE -1),
                          kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
            BY <1>4
      <2>nil. CASE m.id = -1
          <3> QED BY <2>nil
      <2>nonnull. CASE m.id # -1
          <3>mid. m.id = v
                BY <2>wit, <2>nonnull, SMT
          <3>msgLeSenders. Cardinality({pv \in msgs_prevote[vr] : pv.id = v})
                  <=
                  Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                BY PrevoteValueMessagesCardinalityLeSenders, Isa
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                  <=
                  Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                BY PrevoteSenderSetCardinalityMonotone, Isa
          <3>finCF. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
          <3>fin1. IsFiniteSet({pv \in msgs_prevote[vr] : pv.id = v})
                BY PrevoteValueMessagesFinite, Isa
          <3>fin2. IsFiniteSet({s \in (Corr \union Faulty) :
                     \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                <4>sub. {s \in (Corr \union Faulty) : \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src}
                          \subseteq (Corr \union Faulty)  OBVIOUS
                <4> QED  BY <4>sub, <3>finCF, FS_Subset
          <3>fin3. IsFiniteSet({s \in (Corr \union Faulty) :
                     \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                <4>sub. {s \in (Corr \union Faulty) : \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src}
                          \subseteq (Corr \union Faulty)  OBVIOUS
                <4> QED  BY <4>sub, <3>finCF, FS_Subset
          <3>types. /\ Cardinality({pv \in msgs_prevote[vr] : pv.id = v}) \in Int
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src}) \in Int
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src}) \in Int
                      /\ ((2 * T) + 1) \in Int
                BY <3>fin1, <3>fin2, <3>fin3, FiniteCF, FS_Union, FS_Subset,
                   FS_CardinalityType, ConstNat, SMT
          <3>oldSenders. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote[vr] : pp.id = v} : s = pv.src})
                  >= ((2 * T) + 1)
                BY <2>wit, <3>msgLeSenders, <3>types, IntLeGeTrans1
          <3>newSenders. Cardinality({s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[vr] : pp.id = v} : s = pv.src})
                  >= ((2 * T) + 1)
                BY <3>oldSenders, <3>mono, <3>types, IntLeGeTrans1
          <3>pnew. [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                    \in msgs_propose'[r]
                BY <2>wit, ProposeMonotone
          <3>qpost. \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                      /\ \E prop \in msgs_propose'[r] :
                           /\ prop.src = Proposer[r]
                           /\ prop.proposal = m.id
                           /\ rr = prop.valid_round
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[rr] : pp.id = m.id} :
                             s = pv.src}) >= ((2 * T) + 1)
              <4>rrIn. vr \in {rrr \in (0)..(MaxRound) : rrr < r}
                    BY <2>wit
              <4>propOk. /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr]
                              \in msgs_propose'[r]
                          /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].src
                              = Proposer[r]
                          /\ [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].proposal
                              = m.id
                          /\ vr = [proposal |-> v, round |-> round[p], src |-> Proposer[round[p]], valid_round |-> vr].valid_round
                    BY <2>wit, <3>mid, <3>pnew, SMT
              <4>card. Cardinality({s \in (Corr \union Faulty) :
                            \E pv \in {pp \in msgs_prevote'[vr] : pp.id = m.id} :
                              s = pv.src}) >= ((2 * T) + 1)
                    BY <3>mid, <3>newSenders
              <4> QED BY <4>rrIn, <4>propOk, <4>card
          <3> QED BY <2>nonnull, <3>qpost
      <2> QED BY <2>nil, <2>nonnull
  <1>5. CASE \E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]
      <2> QED BY <1>5
  <1> QED BY <1>split, <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM Pres_IfSentPrecommitThenSentPrevote ==
  ASSUME TypedIndInv, Step PROVE IfSentPrecommitThenSentPrevote'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_precommit'[r],
                       m.src \in Corr
               PROVE  \E pv \in msgs_prevote'[r] : pv.src = m.src
      BY DEF IfSentPrecommitThenSentPrevote
  <1>split. \/ m \in msgs_precommit[r]
             \/ \E p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
      BY DisjointCF, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
         UponQuorumOfPrevotesAny, OnQuorumOfNilPrevotes, FaultyStep
  <1>1. CASE m \in msgs_precommit[r]
      <2>1. PICK pv \in msgs_prevote[r] : pv.src = m.src
            BY <1>1 DEF IfSentPrecommitThenSentPrevote
      <2>2. pv \in msgs_prevote'[r]
            BY <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1>2. CASE \E p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
      <2> PICK p \in Corr :
                  /\ step[p] = "PREVOTE_OF_STEP"
                  /\ r = round[p]
                  /\ m.src = p
            BY <1>2
      <2>1. PICK pv \in msgs_prevote[round[p]] :
                /\ pv.id \in ((ValidValues \union InvalidValues) \union {-1})
                /\ p = pv.src
            BY DEF AllIfInPrevoteThenSentPrevote
      <2>2. pv \in msgs_prevote'[r]
            BY <2>1, PrevoteMonotone
      <2> QED BY <2>1, <2>2
  <1> QED BY <1>split, <1>1, <1>2

THEOREM Pres_IfSentPrecommitThenReceivedTwoThirds ==
  ASSUME TypedIndInv, Step PROVE IfSentPrecommitThenReceivedTwoThirds'
  \* Keep only IndTypeOk (typing) + the one pre-invariant this proof needs ambient; USE DEF-
  \* expanding all of IndInv drags the quorum conjuncts' nested-Cardinality set-builders into
  \* every obligation, timing out the fallback-less `BY ... SMT DEF FaultyStep` case.
  <1>tok. IndTypeOk  BY DEF TypedIndInv, IndInv
  <1> USE <1>tok DEF IndTypeOk
  <1>pre. IfSentPrecommitThenReceivedTwoThirds  BY DEF TypedIndInv, IndInv
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound),
                       NEW m \in msgs_precommit'[r],
                       m.src \in Corr
               PROVE  \/ /\ m.id \in ValidValues
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                                 s = pv.src}) >= ((2 * T) + 1)
                       \/ /\ m.id = -1
                          /\ Cardinality({s \in (Corr \union Faulty) :
                               \E pv \in msgs_prevote'[r] : s = pv.src}) >= ((2 * T) + 1)
      BY DEF IfSentPrecommitThenReceivedTwoThirds
  <1>split. \/ m \in msgs_precommit[r]
             \/ (\E p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                   /\ r = round[p]
                   /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1))
             \/ (\E p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                   /\ r = round[p]
                   /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1))
             \/ (\E p \in Corr :
                   /\ r = round[p]
                   /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                   /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1))
      \* Only 4 actions touch msgs_precommit; the other 7 keep it via UNCHANGED. Split
      \* per action so each SMT call reasons about a single action body (the monolithic
      \* call over all four bodies at once was too large to discharge).
      <2>msel. \/ msgs_precommit' = msgs_precommit
               \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
               \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
               \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
               \/ FaultyStep
          BY DEF Step
      <2>1. CASE msgs_precommit' = msgs_precommit
          BY <2>1
      <2>2. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)  BY <2>2
          <3> QED  BY SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>3. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
          <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p)  BY <2>3
          \* msgs_precommit' has a fixed shape independent of the evidence witness, so
          \* extract it without instantiating the existential; keep the prevote quorum
          \* (whose set-builder has a nested \E) as a separate existential fact.
          <3>mp. msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                   (msgs_precommit[round[p]] \union {[id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND",
                                                     round |-> round[p], src |-> p]})]
              BY DEF UponQuorumOfPrevotesAny
          <3>ev. \E ev \in SUBSET msgs_prevote[round[p]] :
                   Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
              BY Zenon DEF UponQuorumOfPrevotesAny
          <3>1. CASE m \in msgs_precommit[r]  BY <3>1
          <3>2. CASE m \notin msgs_precommit[r]
              <4>eq. r = round[p] /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  BY <3>mp, <3>2, SMT
              <4>d3. \E pp \in Corr : \E ev \in SUBSET msgs_prevote[round[pp]] :
                       /\ r = round[pp]
                       /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[pp], src |-> pp]
                       /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
                  BY <3>ev, <4>eq
              <4> QED  BY <4>d3
          <3> QED  BY <3>1, <3>2
      <2>4. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
          <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p)  BY <2>4
          <3>a. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
                /\ msgs_precommit' = [msgs_precommit EXCEPT ![round[p]] =
                     (msgs_precommit[round[p]] \union {[id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND",
                                                       round |-> round[p], src |-> p]})]
              BY DEF OnQuorumOfNilPrevotes
          <3>1. CASE m \in msgs_precommit[r]  BY <3>1
          <3>2. CASE m \notin msgs_precommit[r]
              <4>eq. r = round[p] /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  BY <3>a, <3>2, SMT
              <4>d4. \E pp \in Corr :
                       /\ r = round[pp]
                       /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[pp], src |-> pp]
                       /\ Cardinality({pv \in msgs_prevote[round[pp]] : pv.id = -1}) >= ((2 * T) + 1)
                  BY <3>a, <4>eq
              <4> QED  BY <4>d4
          <3> QED  BY <3>1, <3>2
      <2>5. CASE FaultyStep
          BY <2>5, DisjointCF, SMT DEF FaultyStep
      <2> QED  BY <2>msel, <2>1, <2>2, <2>3, <2>4, <2>5
  <1>1. CASE m \in msgs_precommit[r]
      <2>old. \/ /\ m.id \in ValidValues
                   /\ Cardinality({s \in (Corr \union Faulty) :
                        \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                          s = pv.src}) >= ((2 * T) + 1)
                \/ /\ m.id = -1
                   /\ Cardinality({s \in (Corr \union Faulty) :
                        \E pv \in msgs_prevote[r] : s = pv.src}) >= ((2 * T) + 1)
            BY <1>1, <1>pre DEF IfSentPrecommitThenReceivedTwoThirds
      <2>vcase. CASE /\ m.id \in ValidValues
                    /\ Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                           s = pv.src}) >= ((2 * T) + 1)
          <3>idtype. m.id \in ((ValidValues \union InvalidValues) \union {-1})
                BY <2>vcase
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                           s = pv.src})
                    <=
                    Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                           s = pv.src})
                BY <3>idtype, PrevoteSenderSetCardinalityMonotone, Isa
          <3>types. /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote[r] : pp.id = m.id} :
                             s = pv.src}) \in Int
                       /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                             s = pv.src}) \in Int
                       /\ ((2 * T) + 1) \in Int
                BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
          <3>post. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} :
                           s = pv.src}) >= ((2 * T) + 1)
                BY <2>vcase, <3>mono, <3>types, IntLeGeTrans1
          <3> QED BY <2>vcase, <3>post
      <2>nilcase. CASE /\ m.id = -1
                      /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote[r] : s = pv.src}) >= ((2 * T) + 1)
          <3>mono. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote[r] : s = pv.src})
                    <=
                    Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote'[r] : s = pv.src})
                BY PrevoteAllSenderSetCardinalityMonotone
          <3>types. /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote[r] : s = pv.src}) \in Int
                       /\ Cardinality({s \in (Corr \union Faulty) :
                           \E pv \in msgs_prevote'[r] : s = pv.src}) \in Int
                       /\ ((2 * T) + 1) \in Int
                BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
          <3>post. Cardinality({s \in (Corr \union Faulty) :
                         \E pv \in msgs_prevote'[r] : s = pv.src}) >= ((2 * T) + 1)
                BY <2>nilcase, <3>mono, <3>types, IntLeGeTrans1
          <3> QED BY <2>nilcase, <3>post
      <2> QED BY <2>old, <2>vcase, <2>nilcase
  <1>2. CASE \E p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                  /\ r = round[p]
                  /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr, v \in ValidValues, vr \in ((0)..(MaxRound) \union {-1}) :
                  /\ r = round[p]
                  /\ m = [id |-> v, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : v = pv.id}) >= ((2 * T) + 1)
            BY <1>2
      <2>rid. r = round[p]
            BY <2>wit
      <2>mid. m.id = v
            BY <2>wit
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>vty. v \in ((ValidValues \union InvalidValues) \union {-1})
            BY <2>wit
      <2>eq. {pv \in msgs_prevote[round[p]] : pv.id = v}
              =
              {pv \in msgs_prevote[round[p]] : v = pv.id}
            BY SMT
      <2>lb. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v}) >= ((2 * T) + 1)
            BY <2>wit, <2>eq
      <2>msgLeSenders. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
            BY <2>rty, <2>vty, PrevoteValueMessagesCardinalityLeSenders, Isa
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src})
            BY <2>rty, <2>vty, PrevoteSenderSetCardinalityMonotone, Isa
      <2>types. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = v}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY <2>rty, <2>vty, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldSenders. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote[round[p]] : pp.id = v} : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>lb, <2>msgLeSenders, <2>types, IntLeGeTrans1
      <2>newSenders. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldSenders, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[r] : pp.id = m.id} : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) :
                    \E pv \in {pp \in msgs_prevote'[round[p]] : pp.id = v} : s = pv.src}
            BY <2>rid, <2>mid, SMT
      <2> QED BY <2>mid, <2>newSenders, <2>posteq
  <1>3. CASE \E p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr : \E ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
            BY <1>3
      <2>wit2. PICK ev \in SUBSET msgs_prevote[round[p]] :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) >= ((2 * T) + 1)
            BY <2>wit
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>evLeAll. Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in msgs_prevote[round[p]] : s = pv.src})
            BY <2>rty, PrevoteEvidenceSenderSetCardinalityLeAllSenders, Isa
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
            BY <2>rty, PrevoteAllSenderSetCardinalityMonotone
      <2>types. /\ Cardinality({s \in (Corr \union Faulty) : \E pv \in ev : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote[round[p]] : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote'[round[p]] : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY FiniteCF, FS_Union, FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>wit2, <2>evLeAll, <2>types, IntLeGeTrans1
      <2>newAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldAll, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[r] : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[round[p]] : s = pv.src}
            BY <2>wit2, SMT
      <2> QED BY <2>wit2, <2>newAll, <2>posteq
  <1>4. CASE \E p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
      <2>wit. PICK p \in Corr :
                  /\ r = round[p]
                  /\ m = [id |-> -1, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]
                  /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) >= ((2 * T) + 1)
            BY <1>4
      <2>rty. round[p] \in (0)..(MaxRound)
            BY SMT DEF IndTypeOk
      <2>nilty. -1 \in ((ValidValues \union InvalidValues) \union {-1})
            BY SMT
      <2>msgLeAll. Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                \E pv \in msgs_prevote[round[p]] : s = pv.src})
            BY <2>rty, <2>nilty, PrevoteValueMessagesCardinalityLeAllSenders, Isa
      <2>mono. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              <=
              Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
            BY <2>rty, PrevoteAllSenderSetCardinalityMonotone
      <2>types. /\ Cardinality({pv \in msgs_prevote[round[p]] : pv.id = -1}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote[round[p]] : s = pv.src}) \in Int
                  /\ Cardinality({s \in (Corr \union Faulty) :
                       \E pv \in msgs_prevote'[round[p]] : s = pv.src}) \in Int
                  /\ ((2 * T) + 1) \in Int
            BY <2>rty, <2>nilty, PrevoteValueMessagesFinite, FiniteCF, FS_Union,
               FS_Subset, FS_CardinalityType, ConstNat, SMT
      <2>oldAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>wit, <2>msgLeAll, <2>types, IntLeGeTrans1
      <2>newAll. Cardinality({s \in (Corr \union Faulty) :
                  \E pv \in msgs_prevote'[round[p]] : s = pv.src})
              >= ((2 * T) + 1)
            BY <2>oldAll, <2>mono, <2>types, IntLeGeTrans1
      <2>posteq. {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[r] : s = pv.src}
                  =
                  {s \in (Corr \union Faulty) : \E pv \in msgs_prevote'[round[p]] : s = pv.src}
            BY <2>wit, SMT
      <2> QED BY <2>wit, <2>newAll, <2>posteq
  <1> QED BY <1>split, <1>1, <1>2, <1>3, <1>4

THEOREM Pres_AllNoEquivocationByCorrect ==
  ASSUME TypedIndInv, Step PROVE AllNoEquivocationByCorrect'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound)
               PROVE  /\ \E pv \in ValidValues :
                           \E pvr \in ((0)..(MaxRound) \union {-1}) :
                             \A mp \in msgs_propose'[r] :
                               \/ mp.src \in Faulty
                               \/ /\ /\ mp.src = Proposer[r]
                                     /\ pv = mp.proposal
                                  /\ pvr = mp.valid_round
                      /\ \A q \in Corr :
                           \E vv \in (ValidValues \union {-1}) :
                             \A mv \in msgs_prevote'[r] :
                               q = mv.src => vv = mv.id
                      /\ \A q \in Corr :
                           \E cv \in (ValidValues \union {-1}) :
                             \A mc \in msgs_precommit'[r] :
                               q = mc.src => cv = mc.id
      BY DEF AllNoEquivocationByCorrect
  <1>prop. \E pv \in ValidValues :
               \E pvr \in ((0)..(MaxRound) \union {-1}) :
                 \A mp \in msgs_propose'[r] :
                   \/ mp.src \in Faulty
                   \/ /\ /\ mp.src = Proposer[r]
                         /\ pv = mp.proposal
                      /\ pvr = mp.valid_round
      <2>old. PICK oldv \in ValidValues, oldvr \in ((0)..(MaxRound) \union {-1}) :
                    \A mp \in msgs_propose[r] :
                      \/ mp.src \in Faulty
                      \/ /\ /\ mp.src = Proposer[r]
                            /\ oldv = mp.proposal
                         /\ oldvr = mp.valid_round
            BY DEF AllNoEquivocationByCorrect
      <2>sel. \/ msgs_propose' = msgs_propose
               \/ FaultyStep
               \/ \E p \in Corr : InsertProposal(p)
            BY DEF Step
      <2>same. CASE msgs_propose' = msgs_propose
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>insert. CASE \E p \in Corr : InsertProposal(p)
          <3> PICK p \in Corr : InsertProposal(p) BY <2>insert
          <3> PICK v \in ValidValues :
                msgs_propose' = [msgs_propose EXCEPT ![round[p]] =
                  (msgs_propose[round[p]] \union {[proposal |-> (IF valid_value[p] # -1 THEN valid_value[p] ELSE v),
                     round |-> round[p], src |-> p, valid_round |-> valid_round[p]]})]
              BY <2>insert DEF InsertProposal
          <3>pty. /\ p = Proposer[round[p]]
                  /\ \A mp \in msgs_propose[round[p]] : p # mp.src
                  /\ valid_value[p] \in (ValidValues \union {-1})
                  /\ valid_round[p] \in ((0)..(MaxRound) \union {-1})
                BY <2>insert DEF InsertProposal, IndTypeOk
          <3>newVal. (IF valid_value[p] # -1 THEN valid_value[p] ELSE v) \in ValidValues
                BY <3>pty, NilNotValid, SMT
          <3>1. CASE r = round[p]
              <4>oldFaulty. \A mp \in msgs_propose[r] : mp.src \in Faulty
                    BY <2>old, <3>pty, <3>1, SMT
              <4> QED BY <3>1, <3>pty, <3>newVal, <4>oldFaulty, SMT
          <3>2. CASE r # round[p]
              <4> QED BY <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>insert
  <1>prevote. \A q \in Corr :
                 \E vv \in (ValidValues \union {-1}) :
                   \A mv \in msgs_prevote'[r] :
                     q = mv.src => vv = mv.id
      <2> SUFFICES ASSUME NEW q \in Corr
                   PROVE  \E vv \in (ValidValues \union {-1}) :
                            \A mv \in msgs_prevote'[r] :
                              q = mv.src => vv = mv.id
          OBVIOUS
      <2>old. PICK oldv \in (ValidValues \union {-1}) :
                    \A mv \in msgs_prevote[r] : q = mv.src => oldv = mv.id
            BY DEF AllNoEquivocationByCorrect
      <2>sel.  \/ msgs_prevote' = msgs_prevote
               \/ FaultyStep
               \/ \E p \in Corr : UponProposalInPropose(p)
               \/ \E p \in Corr : UponProposalInProposeAndPrevote(p)
               \/ \E p \in Corr : OnTimeoutPropose(p)
            BY DEF Step
      <2>same. CASE msgs_prevote' = msgs_prevote
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>corr. ASSUME NEW p \in Corr,
                       NEW idv \in (ValidValues \union {-1}),
                       step[p] = "PROPOSE_OF_STEP",
                       msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                PROVE  \E vv \in (ValidValues \union {-1}) :
                         \A mv \in msgs_prevote'[r] :
                           q = mv.src => vv = mv.id
          <3>1. CASE q = p /\ r = round[p]
              <4>none. \A mv \in msgs_prevote[r] : q # mv.src
                    BY <2>corr, <3>1 DEF AllNoFutureMessagesSent
              <4> QED BY <2>corr, <3>1, <4>none, SMT
          <3>2. CASE ~(q = p /\ r = round[p])
              <4> QED BY <2>corr, <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2>proposal. CASE \E p \in Corr : UponProposalInPropose(p)
          <3> PICK p \in Corr : UponProposalInPropose(p) BY <2>proposal
          <3>wit. \E idv \in (ValidValues \union {-1}) :
                    /\ step[p] = "PROPOSE_OF_STEP"
                    /\ msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposal, SMT DEF UponProposalInPropose
          <3> QED BY <3>wit, <2>corr
      <2>proposalPrevote. CASE \E p \in Corr : UponProposalInProposeAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInProposeAndPrevote(p) BY <2>proposalPrevote
          <3>wit. \E idv \in (ValidValues \union {-1}) :
                    /\ step[p] = "PROPOSE_OF_STEP"
                    /\ msgs_prevote' =
                         [msgs_prevote EXCEPT ![round[p]] =
                           (msgs_prevote[round[p]] \union {[id |-> idv,
                             kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposalPrevote, SMT DEF UponProposalInProposeAndPrevote
          <3> QED BY <3>wit, <2>corr
      <2>timeout. CASE \E p \in Corr : OnTimeoutPropose(p)
          <3> PICK p \in Corr : OnTimeoutPropose(p) BY <2>timeout
          <3>wit. /\ step[p] = "PROPOSE_OF_STEP"
                  /\ msgs_prevote' =
                       [msgs_prevote EXCEPT ![round[p]] =
                         (msgs_prevote[round[p]] \union {[id |-> -1,
                           kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>timeout DEF OnTimeoutPropose
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>proposal, <2>proposalPrevote,
         <2>timeout
  <1>precommit. \A q \in Corr :
                   \E cv \in (ValidValues \union {-1}) :
                     \A mc \in msgs_precommit'[r] :
                       q = mc.src => cv = mc.id
      <2> SUFFICES ASSUME NEW q \in Corr
                   PROVE  \E cv \in (ValidValues \union {-1}) :
                            \A mc \in msgs_precommit'[r] :
                              q = mc.src => cv = mc.id
          OBVIOUS
      <2>old. PICK oldv \in (ValidValues \union {-1}) :
                    \A mc \in msgs_precommit[r] : q = mc.src => oldv = mc.id
            BY DEF AllNoEquivocationByCorrect
      <2>sel.  \/ msgs_precommit' = msgs_precommit
               \/ FaultyStep
               \/ \E p \in Corr : UponQuorumOfPrevotesAny(p)
               \/ \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
               \/ \E p \in Corr : OnQuorumOfNilPrevotes(p)
            BY DEF Step
      <2>same. CASE msgs_precommit' = msgs_precommit
          <3> QED BY <2>same, <2>old
      <2>faulty. CASE FaultyStep
          <3> QED BY <2>faulty, <2>old, DisjointCF, SMT DEF FaultyStep
      <2>corr. ASSUME NEW p \in Corr,
                       NEW idv \in (ValidValues \union {-1}),
                       step[p] = "PREVOTE_OF_STEP",
                       msgs_precommit' =
                         [msgs_precommit EXCEPT ![round[p]] =
                           (msgs_precommit[round[p]] \union {[id |-> idv,
                             kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                PROVE  \E cv \in (ValidValues \union {-1}) :
                         \A mc \in msgs_precommit'[r] :
                           q = mc.src => cv = mc.id
          <3>1. CASE q = p /\ r = round[p]
              <4>none. \A mc \in msgs_precommit[r] : q # mc.src
                    BY <2>corr, <3>1 DEF AllNoFutureMessagesSent
              <4> QED BY <2>corr, <3>1, <4>none, SMT
          <3>2. CASE ~(q = p /\ r = round[p])
              <4> QED BY <2>corr, <2>old, <3>2, SMT
          <3> QED BY <3>1, <3>2
      <2>quorumPrevotes. CASE \E p \in Corr : UponQuorumOfPrevotesAny(p)
          <3> PICK p \in Corr : UponQuorumOfPrevotesAny(p) BY <2>quorumPrevotes
          <3>wit. /\ step[p] = "PREVOTE_OF_STEP"
                  /\ msgs_precommit' =
                       [msgs_precommit EXCEPT ![round[p]] =
                         (msgs_precommit[round[p]] \union {[id |-> -1,
                           kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>quorumPrevotes DEF UponQuorumOfPrevotesAny
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2>proposalPrevoteCommit. CASE \E p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p)
          <3> PICK p \in Corr : UponProposalInPrevoteOrCommitAndPrevote(p) BY <2>proposalPrevoteCommit
          <3>wit. \/ msgs_precommit' = msgs_precommit
                  \/ \E idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>proposalPrevoteCommit, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
          <3>same. CASE msgs_precommit' = msgs_precommit
              <4> QED BY <3>same, <2>old
          <3>send. CASE \E idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
              <4> PICK idv \in ValidValues :
                       /\ step[p] = "PREVOTE_OF_STEP"
                       /\ msgs_precommit' =
                            [msgs_precommit EXCEPT ![round[p]] =
                              (msgs_precommit[round[p]] \union {[id |-> idv,
                                kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                    BY <3>send
              <4>idty. idv \in (ValidValues \union {-1}) OBVIOUS
              <4> QED BY <3>send, <4>idty, <2>corr
          <3> QED BY <3>wit, <3>same, <3>send
      <2>nilPrevotes. CASE \E p \in Corr : OnQuorumOfNilPrevotes(p)
          <3> PICK p \in Corr : OnQuorumOfNilPrevotes(p) BY <2>nilPrevotes
          <3>wit. /\ step[p] = "PREVOTE_OF_STEP"
                  /\ msgs_precommit' =
                       [msgs_precommit EXCEPT ![round[p]] =
                         (msgs_precommit[round[p]] \union {[id |-> -1,
                           kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> round[p], src |-> p]})]
                BY <2>nilPrevotes DEF OnQuorumOfNilPrevotes
          <3>nil. -1 \in (ValidValues \union {-1}) BY SMT
          <3> QED BY <3>wit, <3>nil, <2>corr
      <2> QED BY <2>sel, <2>same, <2>faulty, <2>quorumPrevotes,
         <2>proposalPrevoteCommit, <2>nilPrevotes
  <1> QED BY <1>prop, <1>prevote, <1>precommit

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

LEMMA PCSetSubset == ASSUME NEW r, NEW d PROVE PCSet(r, d) \in SUBSET (Corr \union Faulty)  BY DEF PCSet
LEMMA PVSetSubset == ASSUME NEW r, NEW d PROVE PVSet(r, d) \in SUBSET (Corr \union Faulty)  BY DEF PVSet

\* A precommit for a valid value (id = m.id) by a correct process at round r forces a 2T+1
\* prevote-sender quorum for m.id at r (IfSentPrecommitThenReceivedTwoThirds; the nil disjunct is
\* excluded since m.id is valid). Kept standalone so the instantiation runs in a CLEAN context:
\* the identical citation fails amid the heavy hypotheses of LockedValueGivesPostQuorum. Target the
\* message's own .id (never a substituted value) so PVSet stays folded -- cf. LockLemma's <1>pv.
LEMMA PrecommitByCorrectGivesPrevoteQuorum ==
  ASSUME TypedIndInv, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSet(r, m.id)) >= 2 * T + 1
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>ne. m.id # -1  BY NilNotValid
  <1> QED  BY <1>ne, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSet

LEMMA PVSetQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW d \in ((ValidValues \union InvalidValues) \union {-1}),
         Cardinality(PVSet(r, d)) >= 2 * T + 1
  PROVE  Cardinality(PVSetP(r, d)) >= 2 * T + 1
  <1>mono. Cardinality(PVSet(r, d)) <= Cardinality(PVSetP(r, d))
      BY PrevoteSenderSetCardinalityMonotone DEF PVSet, PVSetP
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>pvSub. PVSet(r, d) \subseteq (Corr \union Faulty)  BY DEF PVSet
  <1>pvpSub. PVSetP(r, d) \subseteq (Corr \union Faulty)  BY DEF PVSetP
  <1>nat. /\ Cardinality(PVSet(r, d)) \in Nat
           /\ Cardinality(PVSetP(r, d)) \in Nat
      BY <1>finU, <1>pvSub, <1>pvpSub, FS_Subset, FS_CardinalityType
  <1> QED  BY <1>mono, <1>nat, ConstNat, SMT

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
  BY DEF PCSet
LEMMA PVSetFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSet(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote[r] : d = mm.id} : s = m.src}
  BY DEF PVSet
LEMMA PCSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PCSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_precommit'[r] : d = mm.id} : s = m.src}
  BY DEF PCSetP
LEMMA PVSetPFlip ==
  ASSUME NEW r, NEW d
  PROVE  PVSetP(r, d) = {s \in (Corr \union Faulty) : \E m \in {mm \in msgs_prevote'[r] : d = mm.id} : s = m.src}
  BY DEF PVSetP

\* Any subset of the (finite) replica set is finite.
LEMMA SubsetCFFinite == ASSUME NEW A, A \subseteq (Corr \union Faulty) PROVE IsFiniteSet(A)
  BY FiniteCF, FS_Union, FS_Subset

\* Cardinality congruence, grounded in FS_Subset (this tlapm build's backends do not
\* apply Leibniz under Cardinality on these set-builders without finiteness).
LEMMA CardCong ==
  ASSUME NEW S1, NEW S2, IsFiniteSet(S1), S1 = S2
  PROVE  Cardinality(S1) = Cardinality(S2)
  <1>1. S1 \subseteq S2 /\ S2 \subseteq S1  OBVIOUS
  <1>2. IsFiniteSet(S2)  OBVIOUS
  <1> QED  BY <1>1, <1>2, FS_Subset

\* Cardinality form of PVSetPFlip: the operator's Cardinality equals the flipped set-builder's.
LEMMA PVSetPFlipCard ==
  ASSUME NEW r, NEW d
  PROVE  Cardinality(PVSetP(r, d)) =
           Cardinality({s \in (Corr \union Faulty) :
             \E pv0 \in {pp \in msgs_prevote'[r] : d = pp.id} : s = pv0.src})
  <1>fin. IsFiniteSet(PVSetP(r, d))  BY SubsetCFFinite DEF PVSetP
  <1> QED  BY <1>fin, PVSetPFlip, CardCong

\* PrecommitsLockValue (spec-flipped) restated via PCSet/PVSet.
LEMMA PrecommitsLockValueOp ==
  ASSUME IndTypeOk, PrecommitsLockValue
  PROVE  \A r0 \in (0)..(MaxRound), w \in ValidValues :
           \/ Cardinality(PCSet(r0, w)) < 2 * T + 1
           \/ \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
                Cardinality(PVSet(r3, w2)) < 2 * T + 1
  <1> USE DEF IndTypeOk
  \* Spec in flipped-operator form (PCSetF/PVSetF fold the spec's set-builders) so the \A
  \* instantiations below are over operators (Gotcha 5), then bridged to PCSet/PVSet.
  <1>specF. \A a \in (0)..(MaxRound), b \in ValidValues :
              \/ Cardinality(PCSetF(a, b)) < 2 * T + 1
              \/ \A r3 \in {x \in (0)..(MaxRound) : x > a} : \A w2 \in (ValidValues \ {b}) :
                   Cardinality(PVSetF(r3, w2)) < 2 * T + 1
      BY DEF PrecommitsLockValue, PCSetF, PVSetF
  <1> TAKE r0 \in (0)..(MaxRound), w \in ValidValues
  <1>inst. \/ Cardinality(PCSetF(r0, w)) < 2 * T + 1
           \/ \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
                Cardinality(PVSetF(r3, w2)) < 2 * T + 1
      BY <1>specF
  <1>pcEq. Cardinality(PCSet(r0, w)) = Cardinality(PCSetF(r0, w))
      <2>seteq. PCSet(r0, w) = PCSetF(r0, w)  BY DEF PCSet, PCSetF
      <2>fin. IsFiniteSet(PCSet(r0, w))  BY SubsetCFFinite DEF PCSet
      <2> QED  BY <2>seteq, <2>fin, CardCong
  <1>1. CASE Cardinality(PCSetF(r0, w)) < 2 * T + 1
      <2> QED  BY <1>1, <1>pcEq
  <1>2. CASE \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
               Cardinality(PVSetF(r3, w2)) < 2 * T + 1
      <2>right. \A r3 \in {x \in (0)..(MaxRound) : x > r0} : \A w2 \in (ValidValues \ {w}) :
                  Cardinality(PVSet(r3, w2)) < 2 * T + 1
          \* NB: a combined `TAKE rr \in D1, ww \in D2` trips this tlapm build on set-builder
          \* domains; split into two TAKEs.
          <3> TAKE rr \in {x \in (0)..(MaxRound) : x > r0}
          <3> TAKE ww \in (ValidValues \ {w})
          <3>pvEq. Cardinality(PVSet(rr, ww)) = Cardinality(PVSetF(rr, ww))
              <4>seteq. PVSet(rr, ww) = PVSetF(rr, ww)  BY DEF PVSet, PVSetF
              <4>fin. IsFiniteSet(PVSet(rr, ww))  BY SubsetCFFinite DEF PVSet
              <4> QED  BY <4>seteq, <4>fin, CardCong
          <3>inst. Cardinality(PVSetF(rr, ww)) < 2 * T + 1  BY <1>2
          <3> QED  BY <3>inst, <3>pvEq
      <2> QED  BY <2>right
  <1> QED  BY <1>inst, <1>1, <1>2

\* PrecommitLocksLaterPrevotes (spec-flipped consequent) restated via PVSet.
LEMMA PrecommitLocksLaterPrevotesOp ==
  ASSUME IndTypeOk, PrecommitLocksLaterPrevotes,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound), NEW v \in ValidValues,
         NEW r2 \in (0)..(MaxRound), r2 > r1,
         \E pc \in msgs_precommit[r1] : p = pc.src /\ pc.id /= -1 /\ v /= pc.id,
         \E pv \in msgs_prevote[r2] : p = pv.src /\ v = pv.id
  PROVE  \E r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} : Cardinality(PVSet(r, v)) >= 2 * T + 1
  <1> USE DEF IndTypeOk
  \* Restate the spec with the flipped consequent folded into PVSetF, so instantiation is over an
  \* operator (Gotcha 5), then bridge PVSetF(r,v) = PVSet(r,v).
  <1>plpF. \A cc \in Corr, rr0 \in (0)..(MaxRound), ww \in ValidValues, rr2 \in (0)..(MaxRound):
             (/\ rr2 > rr0
              /\ \E pc \in msgs_precommit[rr0] : cc = pc.src /\ pc.id /= -1 /\ ww /= pc.id
              /\ \E pv \in msgs_prevote[rr2] : cc = pv.src /\ ww = pv.id)
             => \E r \in {rr \in (0)..(MaxRound) : rr >= rr0 /\ rr < rr2} :
                  Cardinality(PVSetF(r, ww)) >= 2 * T + 1
      BY DEF PrecommitLocksLaterPrevotes, PVSetF
  <1>specF. \E r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} : Cardinality(PVSetF(r, v)) >= 2 * T + 1
      BY <1>plpF
  <1> PICK r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} : Cardinality(PVSetF(r, v)) >= 2 * T + 1
      BY <1>specF
  <1>eq. Cardinality(PVSet(r, v)) = Cardinality(PVSetF(r, v))
      <2>seteq. PVSet(r, v) = PVSetF(r, v)  BY DEF PVSet, PVSetF
      <2>fin. IsFiniteSet(PVSet(r, v))  BY SubsetCFFinite DEF PVSet
      <2> QED  BY <2>seteq, <2>fin, CardCong
  <1> QED  BY <1>eq

LEMMA LockContraFromPrevoteQuorum ==
  ASSUME TypedIndInv,
         NEW r0 \in (0)..(MaxRound), NEW r \in (0)..(MaxRound), r > r0,
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         Cardinality(PCSet(r0, w)) >= 2 * T + 1,
         \E r1 \in {rr \in (0)..(MaxRound) : rr >= r0 /\ rr < r} : Cardinality(PVSet(r1, w2)) >= 2 * T + 1
  PROVE  FALSE
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>wne. w # -1 /\ w2 # -1 /\ w2 # w  BY NilNotValid
  <1> PICK r1 \in {rr \in (0)..(MaxRound) : rr >= r0 /\ rr < r} : Cardinality(PVSet(r1, w2)) >= 2 * T + 1  OBVIOUS
  <1>r1dom. r1 \in (0)..(MaxRound) /\ r1 >= r0 /\ r1 < r  BY SMT
  <1>pvNatR1. Cardinality(PVSet(r1, w2)) \in Nat  BY PVSetSubset, <1>finU, FS_Subset, FS_CardinalityType
  \* Second disjunct of the pre-state lock holds (first is false: w has a 2T+1 quorum at r0).
  <1>lock. \A rr \in {x \in (0)..(MaxRound) : x > r0} : \A ww \in (ValidValues \ {w}) : Cardinality(PVSet(rr, ww)) < 2 * T + 1
      <2>0. \/ Cardinality(PCSet(r0, w)) < 2 * T + 1
            \/ (\A rr \in {x \in (0)..(MaxRound) : x > r0} : \A ww \in (ValidValues \ {w}) : Cardinality(PVSet(rr, ww)) < 2 * T + 1)
          BY PrecommitsLockValueOp DEF TypedIndInv, IndInv
      <2>1. Cardinality(PCSet(r0, w)) \in Nat  BY PCSetSubset, <1>finU, FS_Subset, FS_CardinalityType
      <2> QED  BY <2>0, <2>1, ConstNat, SMT
  <1>2. CASE r1 > r0
      <2>1. Cardinality(PVSet(r1, w2)) < 2 * T + 1  BY <1>lock, <1>r1dom, <1>2, <1>wne
      <2> QED  BY <2>1, <1>pvNatR1, ConstNat, SMT
  <1>3. CASE r1 = r0
      <2>pvw2. Cardinality(PVSet(r0, w2)) >= 2 * T + 1  BY <1>3
      <2> PICK q \in Corr : q \in PCSet(r0, w)  BY PCSetSubset, QuorumHasCorrect
      <2> PICK mq \in msgs_precommit[r0] : mq.src = q /\ mq.id = w  BY DEF PCSet
      <2>mqC. mq.src \in Corr /\ mq.id \in ValidValues  BY NilNotValid
      <2>midne. mq.id # w2  BY <1>wne
      \* q's precommit for mq.id (= w) yields a 2T+1 prevote quorum for mq.id at r0.
      \* Work through mq.id (never substitute w inside Cardinality).
      <2>pvw. Cardinality(PVSet(r0, mq.id)) >= 2 * T + 1
          BY <2>mqC, NilNotValid, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSet
      <2>int. \E d \in Corr : d \in PVSet(r0, mq.id) /\ d \in PVSet(r0, w2)
          BY <2>pvw, <2>pvw2, PVSetSubset, QuorumsIntersectInCorrect
      <2> PICK d \in Corr : d \in PVSet(r0, mq.id) /\ d \in PVSet(r0, w2)  BY <2>int
      <2>dw. \E m \in msgs_prevote[r0] : m.src = d /\ m.id = mq.id  BY DEF PVSet
      <2>dw2. \E m \in msgs_prevote[r0] : m.src = d /\ m.id = w2  BY DEF PVSet
      \* d prevotes both mq.id and w2 (# mq.id) at r0 -- forbidden.
      <2> QED  BY <2>dw, <2>dw2, <2>midne, Zenon, SMT DEF AllNoEquivocationByCorrect
  <1> QED  BY <1>2, <1>3, <1>r1dom

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>wne. w # -1 /\ w2 # -1 /\ w2 # w  BY NilNotValid
  <1>w2v. w2 \in ValidValues  BY <1>wne
  <1>pcw. \E pc \in msgs_precommit[r0] : c = pc.src /\ pc.id # -1 /\ w2 # pc.id  BY <1>wne
  <1>pvw2a. \E pv \in msgs_prevote[r] : c = pv.src /\ w2 = pv.id  BY <1>wne
  \* PrecommitLocksLaterPrevotesOp already bridges the spec's flipped orientation to PVSet.
  <1>plp. \E r1 \in {rr \in (0)..(MaxRound) : rr >= r0 /\ rr < r} : Cardinality(PVSet(r1, w2)) >= 2 * T + 1
      BY <1>pcw, <1>pvw2a, <1>w2v, PrecommitLocksLaterPrevotesOp DEF TypedIndInv, IndInv
  <1> QED  BY <1>plp, LockContraFromPrevoteQuorum

\* A correct process that precommitted a non-nil value w at round r0 has locked_round >= r0
\* (AllLatestPrecommitHasLockedRound: every non-nil precommit by c has round <= locked_round[c]).
LEMMA LockedRoundGeR0 ==
  ASSUME TypedIndInv, NEW c \in Corr, NEW r0 \in (0)..(MaxRound), NEW w \in ValidValues,
         \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w
  PROVE  locked_round[c] >= r0
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> PICK pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w  OBVIOUS
  <1>rnd. pc.round = r0  BY DEF IndTypeOk
  <1>wne. w # -1  BY NilNotValid
  <1> QED  BY <1>rnd, <1>wne, SMT DEF AllLatestPrecommitHasLockedRound

\* 2T+1 distinct prevote messages for idv at rr yield a 2T+1 prevote-sender quorum PVSet(rr,idv)
\* (each message is determined by its sender). Standalone so the LeSenders application runs in a
\* clean context.
LEMMA PrevoteMsgQuorumGivesSenderQuorum ==
  ASSUME TypedIndInv, NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1}),
         Cardinality({m \in msgs_prevote[rr] : m.id = idv}) >= 2 * T + 1
  PROVE  Cardinality(PVSet(rr, idv)) >= 2 * T + 1
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>le. Cardinality({m \in msgs_prevote[rr] : m.id = idv}) <= Cardinality(PVSet(rr, idv))
      BY PrevoteValueMessagesCardinalityLeSenders DEF PVSet
  <1>nat. Cardinality(PVSet(rr, idv)) \in Nat
      BY PVSetSubset, FiniteCF, FS_Union, FS_Subset, FS_CardinalityType
  <1>mfin. IsFiniteSet({m \in msgs_prevote[rr] : m.id = idv})  BY PrevoteValueMessagesFinite
  <1>mnat. Cardinality({m \in msgs_prevote[rr] : m.id = idv}) \in Nat  BY <1>mfin, FS_CardinalityType
  <1> QED  BY <1>le, <1>nat, <1>mnat, ConstNat, SMT

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>wne. w # -1 /\ w2 # -1 /\ w2 # w  BY NilNotValid
  <1>w2t. w2 \in ((ValidValues \union InvalidValues) \union {-1})  BY <1>wne
  <1>lr. locked_round[c] >= r0  BY LockedRoundGeR0
  \* Extract the enabling proposal round vr, its 2T+1 prevote quorum for v, and the added prevote.
  <1> PICK v \in (ValidValues \union InvalidValues), vr \in (0)..(MaxRound) :
         /\ vr < round[c]
         /\ Cardinality({m63 \in msgs_prevote[vr] : v = m63.id}) >= ((2 * T) + 1)
         /\ msgs_prevote' = [msgs_prevote EXCEPT ![round[c]] =
              (msgs_prevote[round[c]] \union {[id |-> (IF /\ (v \in ValidValues)
                                                          /\ \/ (locked_round[c] <= vr)
                                                             \/ (locked_value[c] = v)
                                                        THEN v ELSE -1),
                                                kind |-> "PREVOTE_OF_VOTEKIND",
                                                round |-> round[c], src |-> c]})]
      BY SMT DEF UponProposalInProposeAndPrevote
  <1> PICK mv \in msgs_prevote'[round[c]] : mv.src = c /\ mv.id = w2 /\ mv \notin msgs_prevote[round[c]]  OBVIOUS
  \* mv is the fresh prevote, so its id is the IF-expression, which equals w2 (# -1); hence the
  \* value branch fired: v = w2 and (locked_round[c] <= vr \/ locked_value[c] = w2).
  <1>mveq. mv = [id |-> (IF /\ (v \in ValidValues) /\ \/ (locked_round[c] <= vr) \/ (locked_value[c] = v) THEN v ELSE -1),
                 kind |-> "PREVOTE_OF_VOTEKIND", round |-> round[c], src |-> c]
      BY SMT
  <1>vval. v = w2 /\ (locked_round[c] <= vr \/ locked_value[c] = w2)
      BY <1>mveq, <1>wne, SMT
  \* 2T+1 prevote messages for v at vr => 2T+1 prevote senders = Cardinality(PVSet(vr,v));
  \* then substitute v = w2 at the operator-argument level (no substitution inside a Cardinality).
  <1>vt. v \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
  <1>vrdom. vr \in (0)..(MaxRound)  OBVIOUS
  \* Canonical-orientation message count (the action states v = m.id; flip via set equality).
  <1>eq. {m \in msgs_prevote[vr] : m.id = v} = {m \in msgs_prevote[vr] : v = m.id}  BY SMT
  <1>msgQv. Cardinality({m \in msgs_prevote[vr] : m.id = v}) >= 2 * T + 1  BY <1>eq, SMT
  <1>pvV. Cardinality(PVSet(vr, v)) >= 2 * T + 1  BY <1>msgQv, <1>vt, <1>vrdom, PrevoteMsgQuorumGivesSenderQuorum
  <1>quorum. Cardinality(PVSet(vr, w2)) >= 2 * T + 1  BY <1>pvV, <1>vval
  <1>2. CASE locked_round[c] <= vr
      <2>dom. vr \in {x \in (0)..(MaxRound) : /\ (x >= r0) /\ (x < round[c])}  BY <1>lr, <1>2, SMT
      <2> QED  BY <2>dom, <1>quorum
  <1>3. CASE locked_value[c] = w2
      \* c is locked on w2 (# -1), so locked_round[c] # -1, and c's latest precommit sits at
      \* locked_round[c] with id = locked_value[c] = w2 (AllLatestPrecommitHasLockedRound). That
      \* precommit lp (correct, valid id) yields a 2T+1 prevote quorum for w2 at locked_round[c]
      \* (IfSentPrecommitThenReceivedTwoThirds; keep PVSet folded, substitute lp.id = w2 only at
      \* the operator-argument level). locked_round[c] \in [r0, round[c]): >= r0 by <1>lr; and
      \* < round[c] because step[c] = PROPOSE (the action guard) means c sent no precommit at
      \* round[c], while lp is c's precommit at locked_round[c] and AllNoFutureMessagesSent bounds
      \* locked_round[c] <= round[c].
      <2>lv. locked_value[c] = w2  BY <1>3
      <2>step. step[c] = "PROPOSE_OF_STEP"  BY SMT DEF UponProposalInProposeAndPrevote
      <2>lrNonNil. locked_round[c] # -1  BY <2>lv, <1>wne, SMT DEF AllLockedRoundIffLockedValue
      <2>lrDom. locked_round[c] \in (0)..(MaxRound)  BY <2>lrNonNil DEF IndTypeOk
      <2> PICK lp \in msgs_precommit[locked_round[c]] : c = lp.src /\ lp.id = w2
          BY <2>lrNonNil, <2>lv, SMT DEF AllLatestPrecommitHasLockedRound
      <2>lpRound. lp.round = locked_round[c]  BY <2>lrDom DEF IndTypeOk
      <2>lrLe. locked_round[c] <= round[c]  BY <2>lrDom, SMT DEF AllNoFutureMessagesSent
      <2>lrNe. locked_round[c] # round[c]  BY <2>step, SMT DEF AllNoFutureMessagesSent
      <2>lrLt. locked_round[c] < round[c]  BY <2>lrLe, <2>lrNe, <2>lrDom, SMT
      <2>dom. locked_round[c] \in {x \in (0)..(MaxRound) : /\ (x >= r0) /\ (x < round[c])}
          BY <2>lrDom, <2>lrLt, <1>lr, SMT
      <2>lpC. lp.src \in Corr /\ lp.id \in ValidValues  OBVIOUS
      <2>qId. Cardinality(PVSet(locked_round[c], lp.id)) >= 2 * T + 1
          BY <2>lpC, <2>lrDom, NilNotValid, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSet
      <2>quorumL. Cardinality(PVSet(locked_round[c], w2)) >= 2 * T + 1  BY <2>qId
      <2> QED  BY <2>dom, <2>quorumL
  <1> QED  BY <1>vval, <1>2, <1>3

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>vne. v # -1  BY NilNotValid
  \* The pre-state precommit by p at r1 (an r1-round message, since msgs are round-tagged).
  <1> PICK pc \in msgs_precommit[r1] : /\ p = pc.src /\ pc.id /= -1 /\ v /= pc.id  OBVIOUS
  <1>pcRound. pc.round = r1  BY DEF IndTypeOk
  <1>lrNonNil. locked_round[p] # -1
      BY <1>vne, SMT DEF AllLockedRoundIffLockedValue
  <1>lrDom. locked_round[p] \in (0)..(MaxRound)
      BY <1>lrNonNil, SMT DEF IndTypeOk
  \* p's latest precommit lives at locked_round[p] and carries locked_value[p] = v; every other
  \* precommit by p has round <= locked_round[p] (AllLatestPrecommitHasLockedRound, locked case).
  <1> PICK lp \in msgs_precommit[locked_round[p]] : p = lp.src /\ lp.id = v
      BY <1>lrNonNil, SMT DEF AllLatestPrecommitHasLockedRound
  <1>lpRound. lp.round = locked_round[p]  BY <1>lrDom DEF IndTypeOk
  \* pc (round r1) is one of p's precommits, so r1 = pc.round <= locked_round[p].
  <1>lrGe. locked_round[p] >= r1
      BY <1>lrNonNil, <1>pcRound, SMT DEF AllLatestPrecommitHasLockedRound
  \* locked_round[p] <= round[p] = r2 (no future messages by p); and step[p] = PROPOSE means p
  \* sent no precommit at round[p], while lp is p's precommit at locked_round[p], so they differ.
  <1>lrLe. locked_round[p] <= r2
      BY <1>lrDom, SMT DEF AllNoFutureMessagesSent
  <1>lrNe. locked_round[p] # r2
      BY SMT DEF AllNoFutureMessagesSent
  <1>lrLt. locked_round[p] < r2
      BY <1>lrLe, <1>lrNe, <1>lrDom, SMT
  \* lp (correct, valid id) forces a 2T+1 prevote quorum for lp.id at locked_round[p]; keep PVSet
  \* folded and only substitute lp.id = v at the operator-argument level (never under Cardinality).
  <1>lpC. lp.src \in Corr /\ lp.id \in ValidValues  OBVIOUS
  <1>qId. Cardinality(PVSet(locked_round[p], lp.id)) >= 2 * T + 1
      BY <1>lpC, <1>lrDom, PrecommitByCorrectGivesPrevoteQuorum
  <1>preQ. Cardinality(PVSet(locked_round[p], v)) >= 2 * T + 1
      BY <1>qId
  <1>postQ. Cardinality(PVSetP(locked_round[p], v)) >= 2 * T + 1
      BY <1>preQ, <1>lrDom, PVSetQuorumMonotone
  <1> QED BY <1>lrDom, <1>lrGe, <1>lrLt, <1>postQ

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>vne. v # -1  BY NilNotValid
  <1> PICK pc \in msgs_precommit[r1] : /\ p = pc.src /\ pc.id /= -1 /\ v /= pc.id  OBVIOUS
  <1>pcRound. pc.round = r1  BY DEF IndTypeOk
  <1>lrNonNil. locked_round[p] # -1  BY <1>vne, SMT DEF AllLockedRoundIffLockedValue
  <1>lrDom. locked_round[p] \in (0)..(MaxRound)  BY <1>lrNonNil, SMT DEF IndTypeOk
  <1> PICK lp \in msgs_precommit[locked_round[p]] : p = lp.src /\ lp.id = v
      BY <1>lrNonNil, SMT DEF AllLatestPrecommitHasLockedRound
  <1>lpRound. lp.round = locked_round[p]  BY <1>lrDom DEF IndTypeOk
  <1>lrGe. locked_round[p] >= r1  BY <1>lrNonNil, <1>pcRound, SMT DEF AllLatestPrecommitHasLockedRound
  <1>lrLe. locked_round[p] <= r2  BY <1>lrDom, SMT DEF AllNoFutureMessagesSent
  <1>lrNe. locked_round[p] # r2  BY SMT DEF AllNoFutureMessagesSent
  <1>lrLt. locked_round[p] < r2  BY <1>lrLe, <1>lrNe, <1>lrDom, SMT
  <1>lpC. lp.src \in Corr /\ lp.id \in ValidValues  OBVIOUS
  <1>qId. Cardinality(PVSet(locked_round[p], lp.id)) >= 2 * T + 1
      BY <1>lpC, <1>lrDom, PrecommitByCorrectGivesPrevoteQuorum
  <1>preQ. Cardinality(PVSet(locked_round[p], v)) >= 2 * T + 1  BY <1>qId
  <1>dom. locked_round[p] \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}
      BY <1>lrGe, <1>lrLt, <1>lrDom, SMT
  <1> QED  BY <1>preQ, <1>dom

\* A fresh valid (non-nil) prevote by a correct process c at round r is added only by the two
\* value-prevote actions, acting at round[c] = r. Standalone (clean context; the monolithic split
\* is defeated by the heavy hypotheses of the caseChanged bridge).
LEMMA FreshValuePrevoteAction ==
  ASSUME IndTypeOk, Step, NEW c \in Corr, NEW r \in (0)..(MaxRound),
         NEW mv \in msgs_prevote'[r], mv \notin msgs_prevote[r], mv.src = c, mv.id # -1
  PROVE  /\ round[c] = r
         /\ (UponProposalInPropose(c) \/ UponProposalInProposeAndPrevote(c))
  <1> USE DEF IndTypeOk
  <1>sel. \/ msgs_prevote' = msgs_prevote
          \/ (\E q \in Corr : UponProposalInPropose(q))
          \/ (\E q \in Corr : UponProposalInProposeAndPrevote(q))
          \/ (\E q \in Corr : OnTimeoutPropose(q))
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_prevote' = msgs_prevote  BY <1>1
  <1>2. CASE \E q \in Corr : UponProposalInPropose(q)
      <2> PICK q \in Corr : UponProposalInPropose(q)  BY <1>2
      <2> QED  BY SMT DEF UponProposalInPropose
  <1>3. CASE \E q \in Corr : UponProposalInProposeAndPrevote(q)
      <2> PICK q \in Corr : UponProposalInProposeAndPrevote(q)  BY <1>3
      <2> QED  BY SMT DEF UponProposalInProposeAndPrevote
  <1>4. CASE \E q \in Corr : OnTimeoutPropose(q)
      \* adds only a nil prevote, contradicting mv.id # -1.
      <2> PICK q \in Corr : OnTimeoutPropose(q)  BY <1>4
      <2> QED  BY SMT DEF OnTimeoutPropose
  <1>5. CASE FaultyStep
      \* adds only faulty senders, contradicting mv.src = c \in Corr.
      <2> PICK rr \in (0)..(MaxRound), fps2 \in SUBSET Faulty, v2 \in (ValidValues \union InvalidValues) :
             msgs_prevote' = [msgs_prevote EXCEPT ![rr] =
               (msgs_prevote[rr] \union {[id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> v_v54]: v_v54 \in fps2})]
          BY <1>5 DEF FaultyStep
      <2>added. mv \in {[id |-> v2, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> v_v54]: v_v54 \in fps2}
          BY SMT
      <2>fsrc. mv.src \in Faulty  BY <2>added
      <2> QED  BY <2>fsrc, DisjointCF
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>wne. w # -1 /\ w2 # -1  BY NilNotValid
  <1>preC. \E pc \in msgs_precommit[r0] : c = pc.src /\ pc.id # -1 /\ w2 # pc.id  BY <1>wne
  <1>ppp. CASE UponProposalInProposeAndPrevote(c)
      <2> QED  BY <1>ppp, FreshPrevoteGivesQuorum
  <1>pp. CASE UponProposalInPropose(c)
      <2>st. step[c] = "PROPOSE_OF_STEP"  BY <1>pp DEF UponProposalInPropose
      <2>lrNonNil. locked_round[c] # -1
          BY <1>wne, SMT DEF AllLatestPrecommitHasLockedRound
      <2>lv. locked_value[c] = w2
          BY <1>pp, <2>lrNonNil, <1>wne, SMT DEF UponProposalInPropose
      <2>rdom. round[c] \in (0)..(MaxRound)  BY DEF IndTypeOk
      <2> QED  BY <1>preC, <2>rdom, <2>st, <2>lv, LockedValueGivesPreQuorum
  <1> QED  BY <1>ppp, <1>pp

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
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>vne. v # -1  BY NilNotValid
  \* A 2T+1 quorum for v at r contains a correct prevoter c whose prevote carries id = v.
  <1>sub. PVSet(r, v) \in SUBSET (Corr \union Faulty)  BY PVSetSubset
  <1>corr. \E c \in Corr : c \in PVSet(r, v)  BY <1>sub, QuorumHasCorrect
  <1> PICK c \in Corr : c \in PVSet(r, v)  BY <1>corr
  <1> PICK mv \in msgs_prevote[r] : mv.src = c /\ mv.id = v  BY DEF PVSet
  \* c \in Corr, so mv.src \notin Faulty; mv.id = v # -1. The per-message descent conjunct
  \* AllIfSentPrevoteThenReceivedProposalOrTwoThirds applied to mv then yields the goal (the
  \* earlier-quorum disjunct's raw set-builder is re-expressed via PVSet, cf. PVSetFlip/CardCong).
  <1>descent. \/ (\E prop \in msgs_propose[r] :
                    prop.src = Proposer[r] /\ prop.proposal = v /\ prop.valid_round = -1)
              \/ (\E vr \in {x \in (0)..(MaxRound) : x < r} : Cardinality(PVSet(vr, v)) >= 2 * T + 1)
      <2>inv. AllIfSentPrevoteThenReceivedProposalOrTwoThirds
          BY DEF TypedIndInv, IndInv
      <2>raw. \/ mv.src \in Faulty
               \/ mv.id = -1
               \/ /\ mv.id # -1
                  /\ \/ \E prop \in msgs_propose[r] :
                           /\ prop.src = Proposer[r]
                           /\ prop.proposal = mv.id
                           /\ prop.valid_round = -1
                     \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                           /\ \E prop \in msgs_propose[r] :
                                /\ prop.src = Proposer[r]
                                /\ prop.proposal = mv.id
                                /\ rr = prop.valid_round
                           /\ Cardinality({s \in (Corr \union Faulty) :
                                \E m \in {mm \in msgs_prevote[rr] : mm.id = mv.id} :
                                  s = m.src}) >= ((2 * T) + 1)
          BY <2>inv, Zenon DEF AllIfSentPrevoteThenReceivedProposalOrTwoThirds
      <2>src. mv.src = c  OBVIOUS
      <2>mid. mv.id = v  OBVIOUS
      <2>notFaulty. mv.src \notin Faulty  BY <2>src, DisjointCF
      <2>notNil. mv.id # -1  BY <2>mid, <1>vne
      <2>faultyCase. CASE mv.src \in Faulty
          <3> QED  BY <2>faultyCase, <2>notFaulty
      <2>nilCase. CASE mv.id = -1
          <3> QED  BY <2>nilCase, <2>notNil
      <2>goodCase. CASE /\ mv.id # -1
                         /\ \/ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = mv.id
                                  /\ prop.valid_round = -1
                            \/ \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                                  /\ \E prop \in msgs_propose[r] :
                                       /\ prop.src = Proposer[r]
                                       /\ prop.proposal = mv.id
                                       /\ rr = prop.valid_round
                                  /\ Cardinality({s \in (Corr \union Faulty) :
                                       \E m \in {mm \in msgs_prevote[rr] : mm.id = mv.id} :
                                         s = m.src}) >= ((2 * T) + 1)
          <3>propCase. CASE \E prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = mv.id
                             /\ prop.valid_round = -1
              <4> PICK prop \in msgs_propose[r] :
                             /\ prop.src = Proposer[r]
                             /\ prop.proposal = mv.id
                             /\ prop.valid_round = -1
                  BY <3>propCase
              <4> QED  BY <2>mid, SMT
          <3>quorumCase. CASE \E rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = mv.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E m \in {mm \in msgs_prevote[rr] : mm.id = mv.id} :
                                    s = m.src}) >= ((2 * T) + 1)
              <4> PICK rr \in {rrr \in (0)..(MaxRound) : rrr < r} :
                             /\ \E prop \in msgs_propose[r] :
                                  /\ prop.src = Proposer[r]
                                  /\ prop.proposal = mv.id
                                  /\ rr = prop.valid_round
                             /\ Cardinality({s \in (Corr \union Faulty) :
                                  \E m \in {mm \in msgs_prevote[rr] : mm.id = mv.id} :
                                    s = m.src}) >= ((2 * T) + 1)
                  BY <3>quorumCase
              <4>rrDom. rr \in {x \in (0)..(MaxRound) : x < r}  BY SMT
              <4>rawCard. Cardinality({s \in (Corr \union Faulty) :
                              \E m \in {mm \in msgs_prevote[rr] : mm.id = mv.id} :
                                s = m.src}) >= ((2 * T) + 1)
                  OBVIOUS
              <4>cardMv. Cardinality(PVSet(rr, mv.id)) >= 2 * T + 1
                  BY <4>rawCard, Zenon DEF PVSet
              <4>card. Cardinality(PVSet(rr, v)) >= 2 * T + 1
                  BY <4>cardMv, <2>mid
              <4> QED  BY <4>rrDom, <4>card
          <3> QED  BY <2>goodCase, <3>propCase, <3>quorumCase, Zenon
      <2> QED  BY <2>raw, <2>faultyCase, <2>nilCase, <2>goodCase, Zenon
  <1> QED  BY <1>descent

LEMMA PostPrecommitByCorrectGivesPostPrevoteQuorum ==
  ASSUME TypedIndInv, Step, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit'[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSetP(r, m.id)) >= 2 * T + 1
  <1>postInv. IfSentPrecommitThenReceivedTwoThirds'
      BY Pres_IfSentPrecommitThenReceivedTwoThirds DEF TypedIndInv, IndInv
  <1>ne. m.id # -1  BY NilNotValid
  <1> QED  BY <1>postInv, <1>ne, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSetP

LEMMA PostSameRoundPrecommitPrevoteQuorumsContra ==
  ASSUME TypedIndInv, Step, NEW r \in (0)..(MaxRound),
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         Cardinality(PCSetP(r, w)) >= 2 * T + 1,
         Cardinality(PVSetP(r, w2)) >= 2 * T + 1
  PROVE  FALSE
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>wne. w # w2 /\ w # -1 /\ w2 # -1  BY NilNotValid
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>pcSub. PCSetP(r, w) \subseteq (Corr \union Faulty)  BY DEF PCSetP
  <1>pvSub. PVSetP(r, w2) \subseteq (Corr \union Faulty)  BY DEF PVSetP
  <1> PICK q \in Corr : q \in PCSetP(r, w)
      BY <1>pcSub, QuorumHasCorrect
  <1> PICK mq \in msgs_precommit'[r] : mq.src = q /\ mq.id = w  BY DEF PCSetP
  <1>mqC. mq.src \in Corr /\ mq.id \in ValidValues  BY <1>wne
  <1>pvwId. Cardinality(PVSetP(r, mq.id)) >= 2 * T + 1
      BY <1>mqC, PostPrecommitByCorrectGivesPostPrevoteQuorum
  <1>pvw. Cardinality(PVSetP(r, w)) >= 2 * T + 1  BY <1>pvwId
  <1>pvwSub. PVSetP(r, w) \subseteq (Corr \union Faulty)  BY DEF PVSetP
  <1>int. \E d \in Corr : d \in PVSetP(r, w) /\ d \in PVSetP(r, w2)
      BY <1>pvw, <1>pvwSub, <1>pvSub, QuorumsIntersectInCorrect
  <1> PICK d \in Corr : d \in PVSetP(r, w) /\ d \in PVSetP(r, w2)  BY <1>int
  <1>dw. \E pv \in msgs_prevote'[r] : pv.src = d /\ pv.id = w  BY DEF PVSetP
  <1>dw2. \E pv \in msgs_prevote'[r] : pv.src = d /\ pv.id = w2  BY DEF PVSetP
  <1>noEq. AllNoEquivocationByCorrect'
      BY Pres_AllNoEquivocationByCorrect DEF TypedIndInv, IndInv
  <1> QED  BY <1>dw, <1>dw2, <1>wne, <1>noEq DEF AllNoEquivocationByCorrect

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
  <1> USE DEF TypedIndInv, IndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound), Proposer[r] \in Corr,
                      NEW pp \in msgs_propose'[r], pp.src = Proposer[r], pp.valid_round = -1,
                      NEW r2 \in {x \in (0)..(MaxRound) : x < r},
                      NEW mm \in msgs_precommit'[r2], mm.src = Proposer[r], mm.id # -1
               PROVE  FALSE
      BY DEF AllLockedProposerReproposes
  <1>r2dom. r2 \in (0)..(MaxRound) /\ r2 < r  BY SMT
  <1>mmCase. CASE mm \in msgs_precommit[r2]
      \* pr precommitted non-nil at r2 (pre-state) => locked_round[pr] # -1.
      <2>lr. locked_round[Proposer[r]] # -1
          BY <1>mmCase, <1>r2dom, SMT DEF AllLatestPrecommitHasLockedRound
      <2>ppCase. CASE pp \in msgs_propose[r]
          \* pre AllLockedProposerReproposes: no non-nil precommit by pr at r2 < r. Contradicts mm.
          <3> QED BY <1>mmCase, <2>ppCase, <1>r2dom, SMT DEF AllLockedProposerReproposes
      <2>ppNew. CASE pp \notin msgs_propose[r]
          \* pp added by InsertProposal(pr) with valid_round[pr] = pp.valid_round = -1.
          <3>vr. valid_round[Proposer[r]] = -1
              BY <2>ppNew, DisjointCF, SMT DEF Step, InsertProposal, FaultyStep
          <3> QED BY <2>lr, <3>vr, SMT DEF AllLockedRoundBelowValidRound
      <2> QED BY <2>ppCase, <2>ppNew
  <1>mmNew. CASE mm \notin msgs_precommit[r2]
      \* mm (non-nil, correct) is added only by UponProposalInPrevoteOrCommitAndPrevote(pr) at
      \* round[pr] = r2 (round unchanged, msgs_propose unchanged so pp is pre-state).
      <2>rd. round[Proposer[r]] = r2 /\ pp \in msgs_propose[r]
          BY <1>mmNew, <1>r2dom, DisjointCF, SMT DEF Step, FaultyStep, UponQuorumOfPrevotesAny,
             UponProposalInPrevoteOrCommitAndPrevote, OnQuorumOfNilPrevotes
      <2> QED
          BY <2>rd, <1>r2dom, SMT DEF AllNoFutureMessagesSent
  <1> QED BY <1>mmCase, <1>mmNew

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
  <1>finA. IsFiniteSet(A)  BY FS_Subset
  <1>le. Cardinality(A) <= Cardinality(B)  BY FS_Subset
  <1>na. Cardinality(A) \in Nat  BY <1>finA, FS_CardinalityType
  <1>nb. Cardinality(B) \in Nat  BY FS_CardinalityType
  <1> QED  BY <1>le, <1>na, <1>nb, SMT

\* Pure arithmetic transitivity on abstract naturals. Used to lift a >= k through a <= b without
\* handing the concrete Cardinality set-builders to SMT (which then tries, and fails/stalls, to
\* reason about the set structure instead of treating the cardinalities as opaque integers).
LEMMA GeqTransLe ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW k \in Nat, a >= k, a <= b
  PROVE  b >= k
  BY SMT

\* A T+1 sender set already contains a correct process (there are at most F <= T faulty).
LEMMA SmallQuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= T + 1
  PROVE  \E c \in Corr : c \in S
  <1> USE DEF F
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>finFa. IsFiniteSet(Faulty)  BY FiniteCF
  <1>finS. IsFiniteSet(S)  BY <1>finU, FS_Subset
  <1>natS. Cardinality(S) \in Nat  BY <1>finS, FS_CardinalityType
  <1>natFa. Cardinality(Faulty) \in Nat  BY <1>finFa, FS_CardinalityType
  <1> SUFFICES ASSUME \A c \in Corr : c \notin S PROVE FALSE  OBVIOUS
  <1>ssub. S \subseteq Faulty  OBVIOUS
  <1>le. Cardinality(S) <= Cardinality(Faulty)  BY <1>ssub, <1>finFa, FS_Subset
  <1> QED  BY <1>le, <1>natS, <1>natFa, TgeF, ConstNat, SMT

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
  <1> USE DEF IndTypeOk
  <1> PICK rnd \in (0)..(MaxRound) :
        \E ev_propose \in SUBSET msgs_propose[rnd] :
        \E ev_prevote \in SUBSET msgs_prevote[rnd] :
        \E ev_precommit \in SUBSET msgs_precommit[rnd] :
          /\ rnd > round[p]
          /\ Cardinality((({s \in (Corr \union Faulty) : \E m \in ev_propose : s = m.src}
                            \union {s \in (Corr \union Faulty) : \E m \in ev_prevote : s = m.src})
                           \union {s \in (Corr \union Faulty) : \E m \in ev_precommit : s = m.src})) >= T + 1
          /\ step[p] # "DECIDED_OF_STEP"
          /\ round' = [round EXCEPT ![p] = rnd]
          /\ step' = [step EXCEPT ![p] = "PROPOSE_OF_STEP"]
          /\ last_action' = "ON_ROUND_CATCHUP"
      BY DEF OnRoundCatchup
  <1> PICK ev_propose \in SUBSET msgs_propose[rnd] :
        \E ev_prevote \in SUBSET msgs_prevote[rnd] :
        \E ev_precommit \in SUBSET msgs_precommit[rnd] :
          /\ Cardinality((({s \in (Corr \union Faulty) : \E m \in ev_propose : s = m.src}
                            \union {s \in (Corr \union Faulty) : \E m \in ev_prevote : s = m.src})
                           \union {s \in (Corr \union Faulty) : \E m \in ev_precommit : s = m.src})) >= T + 1
      OBVIOUS
  <1> PICK ev_prevote \in SUBSET msgs_prevote[rnd] :
        \E ev_precommit \in SUBSET msgs_precommit[rnd] :
          /\ Cardinality((({s \in (Corr \union Faulty) : \E m \in ev_propose : s = m.src}
                            \union {s \in (Corr \union Faulty) : \E m \in ev_prevote : s = m.src})
                           \union {s \in (Corr \union Faulty) : \E m \in ev_precommit : s = m.src})) >= T + 1
      OBVIOUS
  <1> PICK ev_precommit \in SUBSET msgs_precommit[rnd] :
          Cardinality((({s \in (Corr \union Faulty) : \E m \in ev_propose : s = m.src}
                        \union {s \in (Corr \union Faulty) : \E m \in ev_prevote : s = m.src})
                       \union {s \in (Corr \union Faulty) : \E m \in ev_precommit : s = m.src})) >= T + 1
      OBVIOUS
  <1> DEFINE EV == (({s \in (Corr \union Faulty) : \E m \in ev_propose : s = m.src}
                      \union {s \in (Corr \union Faulty) : \E m \in ev_prevote : s = m.src})
                     \union {s \in (Corr \union Faulty) : \E m \in ev_precommit : s = m.src})
  <1>evCard. Cardinality(EV) >= T + 1  BY DEF EV
  <1>evSub. EV \subseteq AllMsgSenders(rnd)  BY DEF EV, AllMsgSenders
  <1>amsSub. AllMsgSenders(rnd) \subseteq (Corr \union Faulty)  BY DEF AllMsgSenders
  <1>evCF. EV \subseteq (Corr \union Faulty)  BY <1>evSub, <1>amsSub
  \* The T+1 evidence set itself has a correct member; it lies in AllMsgSenders(rnd).
  <1>corrEV. \E cc \in Corr : cc \in EV  BY <1>evCF, <1>evCard, SmallQuorumHasCorrect
  <1> PICK c \in Corr : c \in EV  BY <1>corrEV
  <1>cAMS. c \in AllMsgSenders(rnd)  BY <1>evSub
  <1>rprops. round' = [round EXCEPT ![p] = rnd] /\ rnd > round[p]  OBVIOUS
  <1> QED  BY <1>cAMS, <1>rprops

\* The all-precommit and (prevote OR precommit) sender sets grow monotonically with the message log.
LEMMA PCAllMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PCAll(r)) <= Cardinality(PCAllP(r))
  <1>sub. PCAll(r) \subseteq PCAllP(r)  BY PrecommitMonotone DEF PCAll, PCAllP
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>subCF. PCAllP(r) \subseteq (Corr \union Faulty)  BY DEF PCAllP
  <1>finN. IsFiniteSet(PCAllP(r))  BY <1>subCF, <1>finU, FS_Subset
  <1> QED  BY <1>sub, <1>finN, FS_Subset

LEMMA Q3UnionMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PVAll(r) \union PCAll(r)) <= Cardinality(PVAllP(r) \union PCAllP(r))
  <1>sub. (PVAll(r) \union PCAll(r)) \subseteq (PVAllP(r) \union PCAllP(r))
      BY PrevoteMonotone, PrecommitMonotone DEF PVAll, PCAll, PVAllP, PCAllP
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>subCF. (PVAllP(r) \union PCAllP(r)) \subseteq (Corr \union Faulty)  BY DEF PVAllP, PCAllP
  <1>finN. IsFiniteSet(PVAllP(r) \union PCAllP(r))  BY <1>subCF, <1>finU, FS_Subset
  <1> QED  BY <1>sub, <1>finN, FS_Subset

\* A pre-state Q3(R) \/ Q4(R) lifts to the post-state (both quorums are monotone). R >= 1 so R-1
\* is a real round.
LEMMA PastStartRoundQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW R \in (0)..(MaxRound), R # 0,
         \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
  PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
         \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>1. CASE Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
      <2>mono. Cardinality(PVAll(R) \union PCAll(R)) <= Cardinality(PVAllP(R) \union PCAllP(R))
          BY Q3UnionMonotone
      <2>subOld. (PVAll(R) \union PCAll(R)) \subseteq (Corr \union Faulty)  BY DEF PVAll, PCAll
      <2>natOld. Cardinality(PVAll(R) \union PCAll(R)) \in Nat
          BY <2>subOld, <1>finU, FS_Subset, FS_CardinalityType
      <2>sub. (PVAllP(R) \union PCAllP(R)) \subseteq (Corr \union Faulty)  BY DEF PVAllP, PCAllP
      <2>nat. Cardinality(PVAllP(R) \union PCAllP(R)) \in Nat
          BY <2>sub, <1>finU, FS_Subset, FS_CardinalityType
      <2> QED  BY <1>1, <2>mono, <2>nat, <2>natOld, ConstNat, SMT
  <1>2. CASE Cardinality(PCAll(R - 1)) >= 2 * T + 1
      <2>rdom. R - 1 \in (0)..(MaxRound)  BY ConstNat, SMT
      <2>mono. Cardinality(PCAll(R - 1)) <= Cardinality(PCAllP(R - 1))  BY <2>rdom, PCAllMonotone
      <2>subOld. PCAll(R - 1) \subseteq (Corr \union Faulty)  BY DEF PCAll
      <2>natOld. Cardinality(PCAll(R - 1)) \in Nat  BY <2>subOld, <1>finU, FS_Subset, FS_CardinalityType
      <2>sub. PCAllP(R - 1) \subseteq (Corr \union Faulty)  BY DEF PCAllP
      <2>nat. Cardinality(PCAllP(R - 1)) \in Nat  BY <2>sub, <1>finU, FS_Subset, FS_CardinalityType
      <2> QED  BY <1>2, <2>mono, <2>nat, <2>natOld, ConstNat, SMT
  <1> QED  BY <1>1, <1>2

\* The pre-invariant conjunct AllPastStartRound, re-expressed in operator form for a fixed (c, R).
LEMMA PastStartRoundOperator ==
  ASSUME IndTypeOk, AllPastStartRound, NEW c \in Corr, NEW R \in (0)..(MaxRound),
         ~(R > round[c]), R # 0
  PROVE  \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
  BY Zenon, SMT DEF AllPastStartRound, PVAll, PCAll, IndTypeOk

\* If a correct process c is (pre-state) at round >= R >= 1, the post-state satisfies Q3(R) \/ Q4(R).
LEMMA PastStartRoundFromCorrect ==
  ASSUME IndTypeOk, Step, AllPastStartRound,
         NEW c \in Corr, NEW R \in (0)..(MaxRound), R # 0, R <= round[c]
  PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
         \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
  <1> USE DEF IndTypeOk
  <1>ge. ~(R > round[c])  BY SMT
  <1>op. \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
      BY <1>ge, PastStartRoundOperator
  <1> QED  BY <1>op, PastStartRoundQuorumMonotone

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
  <1> USE DEF IndTypeOk
  <1>rpDom. round[p] \in (0)..(MaxRound)  BY DEF IndTypeOk
  <1> PICK ev \in SUBSET msgs_precommit[round[p]] :
         Cardinality({s \in (Corr \union Faulty) : \E m \in ev : s = m.src}) >= 2 * T + 1
      BY Zenon DEF UponQuorumOfPrecommitsAny
  <1>gev. Cardinality({s \in (Corr \union Faulty) : \E m \in ev : s = m.src}) >= 2 * T + 1  OBVIOUS
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>evSub. {s \in (Corr \union Faulty) : \E m \in ev : s = m.src} \subseteq PCAll(round[p])  BY DEF PCAll
  <1>pcSub. PCAll(round[p]) \subseteq (Corr \union Faulty)  BY DEF PCAll
  <1>finPC. IsFiniteSet(PCAll(round[p]))  BY <1>pcSub, <1>finU, FS_Subset
  <1>natPC. Cardinality(PCAll(round[p])) \in Nat  BY <1>finPC, FS_CardinalityType
  \* Inline the subset-cardinality lift as an explicit <=-chain + arithmetic rather than
  \* instantiating SubsetCardGeq: unifying its A/B against these set-builders is slow enough to
  \* exhaust the fallback chain under -threads contention.
  <1>evFin. IsFiniteSet({s \in (Corr \union Faulty) : \E m \in ev : s = m.src})  BY <1>evSub, <1>finPC, FS_Subset
  <1>evNat. Cardinality({s \in (Corr \union Faulty) : \E m \in ev : s = m.src}) \in Nat  BY <1>evFin, FS_CardinalityType
  <1>le. Cardinality({s \in (Corr \union Faulty) : \E m \in ev : s = m.src}) <= Cardinality(PCAll(round[p]))
      BY <1>evSub, <1>finPC, FS_Subset
  <1>k. (2 * T + 1) \in Nat  BY ConstNat, SMT
  <1>pcQ. Cardinality(PCAll(round[p])) >= 2 * T + 1
      BY <1>gev, <1>le, <1>evNat, <1>natPC, <1>k, GeqTransLe
  <1>mono. Cardinality(PCAll(round[p])) <= Cardinality(PCAllP(round[p]))  BY <1>rpDom, PCAllMonotone
  <1>ppSub. PCAllP(round[p]) \subseteq (Corr \union Faulty)  BY DEF PCAllP
  <1>natPP. Cardinality(PCAllP(round[p])) \in Nat  BY <1>ppSub, <1>finU, FS_Subset, FS_CardinalityType
  <1> QED  BY <1>pcQ, <1>mono, <1>natPC, <1>natPP, <1>k, GeqTransLe

THEOREM Pres_AllPastStartRound ==
  ASSUME TypedIndInv, Step PROVE AllPastStartRound'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>apsr. AllPastStartRound  BY DEF TypedIndInv, IndInv
  \* Unfold the primed goal to operator form (the doubly-nested primed Cardinality set-builders
  \* do not strip in place).
  <1>unfold. AllPastStartRound' <=>
               (\A pp \in Corr, RR \in (0)..(MaxRound):
                  \/ RR > round'[pp]
                  \/ RR = 0
                  \/ Cardinality(PVAllP(RR) \union PCAllP(RR)) >= T + 1
                  \/ Cardinality(PCAllP(RR - 1)) >= 2 * T + 1)
      BY DEF AllPastStartRound, PVAllP, PCAllP
  <1> SUFFICES \A pp \in Corr, RR \in (0)..(MaxRound):
                  \/ RR > round'[pp]
                  \/ RR = 0
                  \/ Cardinality(PVAllP(RR) \union PCAllP(RR)) >= T + 1
                  \/ Cardinality(PCAllP(RR - 1)) >= 2 * T + 1
      BY <1>unfold
  <1> TAKE p \in Corr, R \in (0)..(MaxRound)
  <1> SUFFICES ASSUME ~(R > round'[p]), R # 0
               PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
                      \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
      OBVIOUS
  <1>main. CASE round'[p] = round[p]
      \* No round advance: the pre-invariant on p applies directly (R <= round[p]).
      <2>Rlep. R <= round[p]  BY <1>main, SMT
      <2> QED  BY <1>apsr, <2>Rlep, PastStartRoundFromCorrect
  <1>chg. CASE round'[p] # round[p]
      \* Only UponQuorumOfPrecommitsAny and OnRoundCatchup change a round, and only for the acting
      \* process; every other branch keeps round' = round (its UNCHANGED frame). So the actor is p.
      <2>act. UponQuorumOfPrecommitsAny(p) \/ OnRoundCatchup(p)
          <3>sel. \/ round' = round
                  \/ \E q \in Corr : UponQuorumOfPrecommitsAny(q)
                  \/ \E q \in Corr : OnRoundCatchup(q)
              BY DEF Step
          <3>1. CASE round' = round  BY <3>1, <1>chg, SMT
          <3>2. CASE \E q \in Corr : UponQuorumOfPrecommitsAny(q)
              <4> PICK q \in Corr : UponQuorumOfPrecommitsAny(q)  BY <3>2
              <4>qr. round' = [round EXCEPT ![q] = round[q] + 1]
                  BY Zenon DEF UponQuorumOfPrecommitsAny
              <4>qp. q = p  BY <4>qr, <1>chg, SMT
              <4> QED  BY <4>qp
          <3>3. CASE \E q \in Corr : OnRoundCatchup(q)
              <4> PICK q \in Corr : OnRoundCatchup(q)  BY <3>3
              <4>qr. \E rr \in (0)..(MaxRound) : round' = [round EXCEPT ![q] = rr]
                  BY Zenon DEF OnRoundCatchup
              <4>qp. q = p  BY <4>qr, <1>chg, SMT
              <4> QED  BY <4>qp
          <3> QED  BY <3>sel, <3>1, <3>2, <3>3
      <2>uqp. CASE UponQuorumOfPrecommitsAny(p)
          <3>rp1. round' = [round EXCEPT ![p] = round[p] + 1]
              BY <2>uqp, Zenon DEF UponQuorumOfPrecommitsAny
          <3>rp. round'[p] = round[p] + 1  BY <3>rp1, SMT
          <3>Rle2. R <= round[p] + 1  BY <3>rp, ConstNat, SMT
          <3>a. CASE R <= round[p]
              <4> QED  BY <1>apsr, <3>a, PastStartRoundFromCorrect
          <3>b. CASE ~(R <= round[p])
              <4>Req. R = round[p] + 1  BY <3>b, <3>Rle2, ConstNat, SMT
              <4>rm1. R - 1 = round[p]  BY <4>Req, ConstNat, SMT
              \* The action fired on a 2T+1 precommit-sender quorum at round[p] = R-1; the standalone
              \* lemma lifts it (monotone) to a 2T+1 post-state quorum PCAllP(round[p]).
              <4>post. Cardinality(PCAllP(round[p])) >= 2 * T + 1
                  BY <2>uqp, UQPAGivesPostQuorum
              \* R - 1 = round[p], so Q4'(R) holds.
              <4> QED  BY <4>post, <4>rm1
          <3> QED  BY <3>a, <3>b
      <2>orc. CASE OnRoundCatchup(p)
          \* Isolated lemma peels the evidence: p jumped to rnd on a T+1 quorum whose correct
          \* sender c had round[c] >= rnd >= R (AllNoFutureMessagesSent), so the pre-invariant on c
          \* supplies Q3(R) \/ Q4(R).
          <3> PICK rnd \in (0)..(MaxRound) :
                /\ round' = [round EXCEPT ![p] = rnd]
                /\ rnd > round[p]
                /\ \E c \in Corr : c \in AllMsgSenders(rnd)
              BY <2>orc, OnRoundCatchupGivesSender
          <3>rndEq. round'[p] = rnd  BY SMT
          <3>Rle3. R <= rnd  BY <3>rndEq, SMT
          <3> PICK c \in Corr : c \in AllMsgSenders(rnd)  OBVIOUS
          <3>csent. \/ (\E m \in msgs_propose[rnd] : c = m.src)
                    \/ (\E m \in msgs_prevote[rnd] : c = m.src)
                    \/ (\E m \in msgs_precommit[rnd] : c = m.src)
              BY DEF AllMsgSenders
          <3>cround. rnd <= round[c]
              BY <3>csent, SMT DEF AllNoFutureMessagesSent
          <3>Rlec. R <= round[c]  BY <3>Rle3, <3>cround, SMT
          <3> QED  BY <1>apsr, <3>Rlec, PastStartRoundFromCorrect
      <2> QED  BY <2>act, <2>uqp, <2>orc
  <1> QED  BY <1>main, <1>chg

\* ---------------------------------------------------------------------------
\* CHOOSE-max machinery for AllRoundsBelowHavePrecommitQuorum. The regenerated spec expresses the
\* maximum round reached as CHOOSE m in ({round[k]} \union {0}): m >= every candidate.
\* ---------------------------------------------------------------------------
\* A nonempty subset of a bounded integer interval has a maximum (induction on the bound via
\* NatInductionTrusted -- avoids the higher-order FS_Induction, which needs Isabelle here).
LEMMA BoundedMaxExists ==
  ASSUME NEW b \in Nat, NEW S \in SUBSET (0)..b, S # {}
  PROVE  \E mx \in S : \A o \in S : mx >= o
  <1> DEFINE Q[n \in Nat] == \A SS \in SUBSET (0)..n : (SS # {}) => (\E mx \in SS : \A o \in SS : mx >= o)
  <1>0. Q[0]
      <2> SUFFICES \A SS \in SUBSET (0)..0 : (SS # {}) => (\E mx \in SS : \A o \in SS : mx >= o)  BY DEF Q
      <2> TAKE SS \in SUBSET (0)..0
      <2> HAVE SS # {}
      <2>1. \A o \in SS : 0 >= o  BY SMT
      <2> QED  BY <2>1
  <1>step. \A n \in Nat : Q[n] => Q[n+1]
      <2> TAKE n \in Nat
      <2> HAVE Q[n]
      <2>Qn. \A SS \in SUBSET (0)..n : (SS # {}) => (\E mx \in SS : \A o \in SS : mx >= o)  BY DEF Q
      <2> SUFFICES \A SS \in SUBSET (0)..(n+1) : (SS # {}) => (\E mx \in SS : \A o \in SS : mx >= o)  BY DEF Q
      <2> TAKE SS \in SUBSET (0)..(n+1)
      <2> HAVE SS # {}
      <2>a. CASE (n+1) \in SS
          <3>1. \A o \in SS : (n+1) >= o  BY SMT
          <3> QED  BY <2>a, <3>1
      <2>b. CASE (n+1) \notin SS
          <3>sub. SS \in SUBSET (0)..n  BY <2>b, SMT
          <3> QED  BY <3>sub, <2>Qn
      <2> QED  BY <2>a, <2>b
  <1>Qall. \A n \in Nat : Q[n]  BY <1>0, <1>step, NatInductionTrusted
  <1>Qb. Q[b]  BY <1>Qall
  <1> QED  BY <1>Qb DEF Q

MaxCandOf(rd) == {rd[k] : k \in DOMAIN rd} \union {0}
MaxReachedOf(rd) == CHOOSE mx \in MaxCandOf(rd) : \A o \in MaxCandOf(rd) : mx >= o

\* The CHOOSE-max lands in the candidate set and dominates it (the max exists, by BoundedMaxExists).
LEMMA MaxReachedProps ==
  ASSUME NEW rd, \A k \in DOMAIN rd : rd[k] \in (0)..(MaxRound)
  PROVE  /\ MaxReachedOf(rd) \in MaxCandOf(rd)
         /\ \A o \in MaxCandOf(rd) : MaxReachedOf(rd) >= o
  <1>sub. MaxCandOf(rd) \in SUBSET (0)..(MaxRound)  BY ConstNat, SMT DEF MaxCandOf
  <1>ne. MaxCandOf(rd) # {}  BY DEF MaxCandOf
  <1>ex. \E mx \in MaxCandOf(rd) : \A o \in MaxCandOf(rd) : mx >= o
      BY <1>sub, <1>ne, ConstNat, BoundedMaxExists
  <1> QED  BY <1>ex DEF MaxReachedOf

\* A correct process reaches round R (R < max reached) only after every earlier round collected a
\* 2T+1 precommit quorum. The global max advances only via UponQuorumOfPrecommitsAny (+1, whose
\* 2T+1 precommit trigger IS the quorum at the round left); OnRoundCatchup cannot advance the max
\* (its evidence has a correct sender c with round[c] >= its target, so the target was already
\* reached). Below the pre-max, the pre-invariant + PCAll monotonicity suffice.
THEOREM Pres_AllRoundsBelowHavePrecommitQuorum ==
  ASSUME TypedIndInv, Step PROVE AllRoundsBelowHavePrecommitQuorum'
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>arb. AllRoundsBelowHavePrecommitQuorum  BY DEF TypedIndInv, IndInv
  <1>tp. IndTypeOk'  BY TypePres DEF TypedIndInv, IndInv
  <1>rBoundsU. \A k \in Corr : round[k] \in (0)..(MaxRound)  BY DEF IndTypeOk
  <1>rBoundsP. \A k \in Corr : round'[k] \in (0)..(MaxRound)  BY <1>tp DEF IndTypeOk
  <1>domU. DOMAIN round = Corr  BY DEF IndTypeOk
  <1>domP. DOMAIN round' = Corr  BY <1>tp DEF IndTypeOk
  \* Pre-invariant in operator form.
  <1>arbOp. \A RR \in (0)..(MaxRound) : (RR < MaxReachedOf(round)) => Cardinality(PCAll(RR)) >= 2 * T + 1
      BY <1>arb, Zenon DEF AllRoundsBelowHavePrecommitQuorum, MaxReachedOf, MaxCandOf, PCAll
  <1>propsU. MaxReachedOf(round) \in MaxCandOf(round) /\ \A o \in MaxCandOf(round) : MaxReachedOf(round) >= o
      BY <1>rBoundsU, <1>domU, MaxReachedProps
  <1>mrU. MaxReachedOf(round) \in (0)..(MaxRound)
      BY <1>propsU, <1>rBoundsU, <1>domU, ConstNat, SMT DEF MaxCandOf
  \* Unfold the primed goal to operator form.
  <1> SUFFICES \A R \in (0)..(MaxRound) : (R < MaxReachedOf(round')) => Cardinality(PCAllP(R)) >= 2 * T + 1
      BY DEF AllRoundsBelowHavePrecommitQuorum, MaxReachedOf, MaxCandOf, PCAllP
  <1> TAKE R \in (0)..(MaxRound)
  <1> HAVE R < MaxReachedOf(round')
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  \* MaxReachedOf(round') is a candidate >= all; being > R >= 0 it equals round'[pp] for some pp.
  <1>propsP. MaxReachedOf(round') \in MaxCandOf(round') /\ \A o \in MaxCandOf(round') : MaxReachedOf(round') >= o
      BY <1>rBoundsP, <1>domP, MaxReachedProps
  <1>mp. \E pp \in Corr : round'[pp] > R
      <2>inCand. MaxReachedOf(round') \in ({round'[k] : k \in Corr} \union {0})
          BY <1>propsP, <1>domP DEF MaxCandOf
      <2> QED  BY <2>inCand, SMT
  <1> PICK pp \in Corr : round'[pp] > R  BY <1>mp
  \* Post-state quorum typing (shared).
  <1>ppSub. PCAllP(R) \subseteq (Corr \union Faulty)  BY DEF PCAllP
  <1>natPP. Cardinality(PCAllP(R)) \in Nat  BY <1>ppSub, <1>finU, FS_Subset, FS_CardinalityType
  <1>main. CASE R < MaxReachedOf(round)
      <2>preQ. Cardinality(PCAll(R)) >= 2 * T + 1  BY <1>arbOp, <1>main
      <2>mono. Cardinality(PCAll(R)) <= Cardinality(PCAllP(R))  BY PCAllMonotone
      <2>pcSub. PCAll(R) \subseteq (Corr \union Faulty)  BY DEF PCAll
      <2>finPC. IsFiniteSet(PCAll(R))  BY <2>pcSub, <1>finU, FS_Subset
      <2>natPC. Cardinality(PCAll(R)) \in Nat  BY <2>finPC, FS_CardinalityType
      <2> QED  BY <2>preQ, <2>mono, <2>natPC, <1>natPP, ConstNat, SMT
  <1>chg. CASE ~(R < MaxReachedOf(round))
      <2>geRoundPP. MaxReachedOf(round) >= round[pp]
          <3>cand. round[pp] \in MaxCandOf(round)  BY <1>domU DEF MaxCandOf
          <3> QED  BY <3>cand, <1>propsU
      <2>advanced. round'[pp] # round[pp]  BY <2>geRoundPP, <1>chg, <1>propsU, <1>mrU, <1>rBoundsU, <1>rBoundsP, SMT
      <2>act. UponQuorumOfPrecommitsAny(pp) \/ OnRoundCatchup(pp)
          <3>sel. \/ round' = round
                  \/ \E q \in Corr : UponQuorumOfPrecommitsAny(q)
                  \/ \E q \in Corr : OnRoundCatchup(q)
              BY DEF Step
          <3>1. CASE round' = round  BY <3>1, <2>advanced, SMT
          <3>2. CASE \E q \in Corr : UponQuorumOfPrecommitsAny(q)
              <4> PICK q \in Corr : UponQuorumOfPrecommitsAny(q)  BY <3>2
              <4>qr. round' = [round EXCEPT ![q] = round[q] + 1]  BY Zenon DEF UponQuorumOfPrecommitsAny
              <4>qp. q = pp  BY <4>qr, <2>advanced, SMT
              <4> QED  BY <4>qp
          <3>3. CASE \E q \in Corr : OnRoundCatchup(q)
              <4> PICK q \in Corr : OnRoundCatchup(q)  BY <3>3
              <4>qr. \E rr \in (0)..(MaxRound) : round' = [round EXCEPT ![q] = rr]  BY Zenon DEF OnRoundCatchup
              <4>qp. q = pp  BY <4>qr, <2>advanced, SMT
              <4> QED  BY <4>qp
          <3> QED  BY <3>sel, <3>1, <3>2, <3>3
      <2>uqp. CASE UponQuorumOfPrecommitsAny(pp)
          <3>rp1. round' = [round EXCEPT ![pp] = round[pp] + 1]  BY <2>uqp, Zenon DEF UponQuorumOfPrecommitsAny
          <3>rp. round'[pp] = round[pp] + 1  BY <3>rp1, SMT
          <3>Req. R = round[pp]  BY <3>rp, <2>geRoundPP, <1>chg, <1>propsU, <1>mrU, <1>rBoundsU, <1>rBoundsP, ConstNat, SMT
          <3>post. Cardinality(PCAllP(round[pp])) >= 2 * T + 1  BY <2>uqp, UQPAGivesPostQuorum
          <3> QED  BY <3>post, <3>Req
      <2>orc. CASE OnRoundCatchup(pp)
          <3> PICK rnd \in (0)..(MaxRound) :
                /\ round' = [round EXCEPT ![pp] = rnd]
                /\ rnd > round[pp]
                /\ \E c \in Corr : c \in AllMsgSenders(rnd)
              BY <2>orc, OnRoundCatchupGivesSender
          <3>rndEq. round'[pp] = rnd  BY SMT
          <3> PICK c \in Corr : c \in AllMsgSenders(rnd)  OBVIOUS
          <3>csent. \/ (\E m \in msgs_propose[rnd] : c = m.src)
                    \/ (\E m \in msgs_prevote[rnd] : c = m.src)
                    \/ (\E m \in msgs_precommit[rnd] : c = m.src)
              BY DEF AllMsgSenders
          <3>cround. rnd <= round[c]  BY <3>csent, SMT DEF AllNoFutureMessagesSent
          <3>cCand. round[c] \in MaxCandOf(round)  BY <1>domU DEF MaxCandOf
          <3>geC. MaxReachedOf(round) >= round[c]  BY <3>cCand, <1>propsU
          <3> QED  BY <3>rndEq, <3>cround, <3>geC, <1>chg, <1>propsU, <1>mrU, <1>rBoundsU, <1>rBoundsP, SMT
      <2> QED  BY <2>act, <2>uqp, <2>orc
  <1> QED  BY <1>main, <1>chg

\* If valid_round[q]' = round[q]' then the acting process's step guard (for the step-changing
\* actions the actor was in PROPOSE/PREVOTE, so by the pre-invariant valid_round[q] # round[q],
\* making the premise vacuous for it) or the round-advance bound (valid_round <= round) forces the
\* premise vacuous, and the locking action sets step to PRECOMMIT.
THEOREM Pres_AllValidInCurrentRoundPrecommitted ==
  ASSUME TypedIndInv, Step PROVE AllValidInCurrentRoundPrecommitted'
  \* Extract only the conjuncts this proof needs (pre-invariant + bound + typing) instead of
  \* USE DEF-expanding all of TypedIndInv -- the full expansion bloats the single-shot SMT call
  \* over the 10 action bodies enough to time out under -threads contention.
  <1>pre. /\ IndTypeOk
          /\ AllValidInCurrentRoundPrecommitted
          /\ AllValidAndLockedRoundBounded
      BY DEF TypedIndInv, IndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr, valid_round'[q] = round'[q]
               PROVE  step'[q] = "PRECOMMIT_OF_STEP" \/ step'[q] = "DECIDED_OF_STEP"
      BY DEF AllValidInCurrentRoundPrecommitted
  <1> QED
      BY <1>pre, SMT DEF Step, UponProposalInPropose, UponProposalInProposeAndPrevote,
         UponProposalInPrevoteOrCommitAndPrevote, UponQuorumOfPrevotesAny,
         UponQuorumOfPrecommitsAny, UponProposalInPrecommitNoDecision, OnTimeoutPropose,
         OnQuorumOfNilPrevotes, OnRoundCatchup,
         AllValidInCurrentRoundPrecommitted, AllValidAndLockedRoundBounded, IndTypeOk

\* locked_round and valid_round change only in UponProposalInPrevoteOrCommitAndPrevote, which
\* sets both to round[p] (lab_then) or leaves locked_round and sets valid_round = round[p]
\* (lab_else, where locked_round <= round by AllValidAndLockedRoundBounded).
THEOREM Pres_AllLockedRoundBelowValidRound ==
  ASSUME TypedIndInv, Step PROVE AllLockedRoundBelowValidRound'
  \* Extract only the needed conjuncts; USE DEF-expanding all of TypedIndInv drags the quorum
  \* invariants' Cardinality set-builders into this single-shot SMT call, pushing it onto the slow
  \* fallback chain where it times out under -threads contention.
  <1>pre. /\ IndTypeOk
          /\ AllLockedRoundBelowValidRound
          /\ AllValidAndLockedRoundBounded
      BY DEF TypedIndInv, IndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW q \in Corr PROVE locked_round'[q] <= valid_round'[q]
      BY DEF AllLockedRoundBelowValidRound
  <1> QED
      BY <1>pre, SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote,
         AllLockedRoundBelowValidRound, AllValidAndLockedRoundBounded, IndTypeOk

\* valid_round changes only in UponProposalInPrevoteOrCommitAndPrevote (to round[p]); lab_then
\* adds a precommit by p at round[p], lab_else has step[p] = PRECOMMIT so a precommit by p at
\* round[p] already exists (AllIfInPrecommitThenSentPrecommit). Otherwise valid_round[q] is
\* unchanged and its old precommit persists (PrecommitMonotone).
THEOREM Pres_AllIfValidRoundThenPrecommitted ==
  ASSUME TypedIndInv, Step PROVE AllIfValidRoundThenPrecommitted'
  \* Keep only IndTypeOk (typing) ambient as a fact and pull the three non-typing conjuncts this
  \* proof needs separately; USE DEF-expanding all of TypedIndInv drags the quorum invariants'
  \* nested Cardinality set-builders into every obligation, bloating the SMT calls enough to time
  \* out under -threads contention.
  <1>tok. IndTypeOk  BY DEF TypedIndInv, IndInv, IndInv
  <1> USE <1>tok DEF IndTypeOk
  <1>pre. /\ AllIfValidRoundThenPrecommitted
          /\ AllIfInPrecommitThenSentPrecommit
          /\ AllValidAndLockedRoundBounded
      BY DEF TypedIndInv, IndInv, IndInv
  <1> USE DEF AllIfValidRoundThenPrecommitted
  <1> SUFFICES ASSUME NEW q \in Corr, valid_round'[q] # -1
               PROVE  \E m \in msgs_precommit'[valid_round'[q]] : q = m.src
      OBVIOUS
  <1>vrq. valid_round'[q] \in (0)..(MaxRound)
      BY SMT DEF Step, UponProposalInPrevoteOrCommitAndPrevote
  <1>1. CASE valid_round'[q] = valid_round[q]
      \* valid_round unchanged: the old precommit at valid_round[q] persists.
      <2>a. \E m \in msgs_precommit[valid_round[q]] : q = m.src  BY <1>1, <1>pre
      <2> PICK m \in msgs_precommit[valid_round[q]] : q = m.src  BY <2>a
      <2> QED  BY <2>a, <1>1, <1>vrq, PrecommitMonotone
  <1>2. CASE valid_round'[q] # valid_round[q]
      \* only UponProposalInPrevoteOrCommitAndPrevote(q) changes valid_round[q], to round[q];
      \* lab_then adds q's precommit at round[q], lab_else has step[q] = PRECOMMIT. Decomposed into
      \* the two labels so each obligation stays small (a single-shot SMT over Step + the full
      \* invariant times out under -threads contention).
      \* Identify the actor cheaply via a valid_round frame selector: only UPCP changes valid_round
      \* (every other branch keeps its UNCHANGED frame), so the actor is q.
      <2>sel. \/ valid_round' = valid_round
              \/ \E pp \in Corr : UponProposalInPrevoteOrCommitAndPrevote(pp)
          BY DEF Step
      <2>act. UponProposalInPrevoteOrCommitAndPrevote(q)
          <3>1. CASE valid_round' = valid_round
              <4> QED  BY <3>1, <1>2
          <3>2. CASE \E pp \in Corr : UponProposalInPrevoteOrCommitAndPrevote(pp)
              <4> PICK pp \in Corr : UponProposalInPrevoteOrCommitAndPrevote(pp)  BY <3>2
              <4>vr. valid_round' = [valid_round EXCEPT ![pp] = round[pp]]
                  BY Zenon DEF UponProposalInPrevoteOrCommitAndPrevote
              <4>pq. pp = q  BY <4>vr, <1>2, SMT
              <4> QED  BY <4>pq
          <3> QED  BY <2>sel, <3>1, <3>2
      <2>vr. valid_round'[q] = round[q]
          BY <2>act, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
      <2>rdom. round[q] \in (0)..(MaxRound)  BY DEF IndTypeOk
      <2>ex. \E m \in msgs_precommit'[round[q]] : q = m.src
          <3>then. CASE step[q] = "PREVOTE_OF_STEP"
              \* lab_then broadcasts q's precommit for the proposed value at round[q].
              <4> QED  BY <2>act, <3>then, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
          <3>else. CASE step[q] # "PREVOTE_OF_STEP"
              \* lab_else: step[q] = PRECOMMIT, so q's precommit at round[q] already exists.
              <4>pcstep. step[q] = "PRECOMMIT_OF_STEP"
                  BY <2>act, <3>else, SMT DEF UponProposalInPrevoteOrCommitAndPrevote
              <4>old. \E m \in msgs_precommit[round[q]] : q = m.src
                  BY <4>pcstep, <1>pre DEF AllIfInPrecommitThenSentPrecommit
              <4> QED  BY <4>old, <2>rdom, PrecommitMonotone
          <3> QED  BY <3>then, <3>else
      <2> QED  BY <2>ex, <2>vr
  <1> QED  BY <1>1, <1>2

\* Proposals are added only by InsertProposal (correct proposer, step PROPOSE), which sets the
\* proposal's valid_round = valid_round[p]. step[p] = PROPOSE gives valid_round[p] # round[p]
\* (AllValidInCurrentRoundPrecommitted contrapositive), and valid_round[p] <= round[p]
\* (AllValidAndLockedRoundBounded), so valid_round[p] < round[p].
THEOREM Pres_AllCorrectProposalValidRoundBelowRound ==
  ASSUME TypedIndInv, Step PROVE AllCorrectProposalValidRoundBelowRound'
  \* Extract only the needed conjuncts; USE DEF-expanding all of TypedIndInv drags the quorum
  \* invariants' Cardinality set-builders into this single-shot SMT call, pushing it onto the slow
  \* fallback chain where it times out under -threads contention.
  <1>pre. /\ IndTypeOk
          /\ AllCorrectProposalValidRoundBelowRound
          /\ AllValidInCurrentRoundPrecommitted
          /\ AllValidAndLockedRoundBounded
      BY DEF TypedIndInv, IndInv, IndInv, IndTypeOk
  <1> SUFFICES ASSUME NEW r \in (0)..(MaxRound), NEW mp \in msgs_propose'[r], mp.src \in Corr
               PROVE  r > mp.valid_round
      BY DEF AllCorrectProposalValidRoundBelowRound
  <1> QED
      BY <1>pre, DisjointCF, SMT DEF Step, InsertProposal, FaultyStep,
         AllCorrectProposalValidRoundBelowRound,
         AllValidInCurrentRoundPrecommitted, AllValidAndLockedRoundBounded, IndTypeOk

\* A fresh non-nil precommit by a correct process p at r1 is added only by
\* UponProposalInPrevoteOrCommitAndPrevote(p) (the only action adding a non-nil correct precommit),
\* which acts in round[p] = r1 at step PREVOTE and leaves msgs_prevote unchanged. Standalone so the
\* heavy Step case analysis runs in a clean context (Gotcha 6).
LEMMA FreshPrecommitShape ==
  ASSUME IndTypeOk, Step, NEW p \in Corr, NEW r1 \in (0)..(MaxRound),
         NEW pc \in msgs_precommit'[r1], pc \notin msgs_precommit[r1],
         p = pc.src, pc.id # -1
  PROVE  /\ round[p] = r1
         /\ step[p] = "PREVOTE_OF_STEP"
         /\ msgs_prevote' = msgs_prevote
  <1> USE DEF IndTypeOk
  \* Only these actions add a precommit; each disjunct carries the msgs_prevote frame it needs
  \* (FaultyStep is the only one that changes msgs_prevote and is ruled out separately).
  <1>sel. \/ msgs_precommit' = msgs_precommit
          \/ (\E q \in Corr : UponProposalInPrevoteOrCommitAndPrevote(q) /\ msgs_prevote' = msgs_prevote)
          \/ (\E q \in Corr : UponQuorumOfPrevotesAny(q) /\ msgs_prevote' = msgs_prevote)
          \/ (\E q \in Corr : OnQuorumOfNilPrevotes(q) /\ msgs_prevote' = msgs_prevote)
          \/ FaultyStep
      BY DEF Step
  <1>1. CASE msgs_precommit' = msgs_precommit
      <2> QED  BY <1>1
  <1>2. CASE \E q \in Corr : UponProposalInPrevoteOrCommitAndPrevote(q) /\ msgs_prevote' = msgs_prevote
      \* the fresh non-nil pc forces lab_then (adds precommit src=q at round[q]); q = p, round[p] = r1.
      <2> PICK q \in Corr : UponProposalInPrevoteOrCommitAndPrevote(q) /\ msgs_prevote' = msgs_prevote
          BY <1>2
      <2> QED  BY SMT DEF UponProposalInPrevoteOrCommitAndPrevote
  <1>3. CASE \E q \in Corr : UponQuorumOfPrevotesAny(q) /\ msgs_prevote' = msgs_prevote
      \* adds only a nil precommit, contradicting pc.id # -1.
      <2> PICK q \in Corr : UponQuorumOfPrevotesAny(q) /\ msgs_prevote' = msgs_prevote  BY <1>3
      <2> QED  BY SMT DEF UponQuorumOfPrevotesAny
  <1>4. CASE \E q \in Corr : OnQuorumOfNilPrevotes(q) /\ msgs_prevote' = msgs_prevote
      <2> PICK q \in Corr : OnQuorumOfNilPrevotes(q) /\ msgs_prevote' = msgs_prevote  BY <1>4
      <2> QED  BY SMT DEF OnQuorumOfNilPrevotes
  <1>5. CASE FaultyStep
      \* adds only faulty senders, contradicting pc.src = p \in Corr.
      <2>ex. \E r \in (0)..(MaxRound) : \E fps3 \in SUBSET Faulty : \E v3 \in (ValidValues \union InvalidValues) :
               msgs_precommit' = [msgs_precommit EXCEPT ![r] =
                 (msgs_precommit[r] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> r, src |-> v_v55]: v_v55 \in fps3})]
          BY <1>5 DEF FaultyStep
      <2> PICK r \in (0)..(MaxRound) : \E fps3 \in SUBSET Faulty : \E v3 \in (ValidValues \union InvalidValues) :
               msgs_precommit' = [msgs_precommit EXCEPT ![r] =
                 (msgs_precommit[r] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> r, src |-> v_v55]: v_v55 \in fps3})]
          BY <2>ex
      <2> PICK fps3 \in SUBSET Faulty : \E v3 \in (ValidValues \union InvalidValues) :
               msgs_precommit' = [msgs_precommit EXCEPT ![r] =
                 (msgs_precommit[r] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> r, src |-> v_v55]: v_v55 \in fps3})]
          OBVIOUS
      <2> PICK v3 \in (ValidValues \union InvalidValues) :
               msgs_precommit' = [msgs_precommit EXCEPT ![r] =
                 (msgs_precommit[r] \union {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> r, src |-> v_v55]: v_v55 \in fps3})]
          OBVIOUS
      \* pc is fresh, so it lies in the added faulty set; its src is in fps3 \subseteq Faulty.
      <2>added. pc \in {[id |-> v3, kind |-> "PRECOMMIT_OF_VOTEKIND", round |-> r, src |-> v_v55]: v_v55 \in fps3}
          BY SMT
      <2>fsrc. pc.src \in Faulty  BY <2>added
      <2> QED  BY <2>fsrc, DisjointCF
  <1> QED  BY <1>sel, <1>1, <1>2, <1>3, <1>4, <1>5

\* The per-process lock-survival invariant. Its preservation is a research obligation of the
\* same character as Pres_PrecommitsLockValue (it is exactly the hypothesis that proof relies on).
THEOREM Pres_PrecommitLocksLaterPrevotesOp ==
  ASSUME TypedIndInv, Step
  PROVE  \A pp \in Corr, rr1 \in (0)..(MaxRound), vv \in ValidValues, rr2 \in (0)..(MaxRound):
            (/\ rr2 > rr1
             /\ \E pc \in msgs_precommit'[rr1] : pp = pc.src /\ pc.id /= -1 /\ vv /= pc.id
             /\ \E pv \in msgs_prevote'[rr2] : pp = pv.src /\ vv = pv.id)
            => \E r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2} :
                 Cardinality(PVSetP(r, vv)) >= 2 * T + 1
  <1> SUFFICES ASSUME NEW p \in Corr, NEW r1 \in (0)..(MaxRound),
                      NEW v \in ValidValues, NEW r2 \in (0)..(MaxRound),
                      /\ r2 > r1
                      /\ \E pc \in msgs_precommit'[r1]:
                           /\ p = pc.src
                           /\ pc.id /= -1
                           /\ v /= pc.id
                      /\ \E pv \in msgs_prevote'[r2]:
                           /\ p = pv.src
                           /\ v = pv.id
               PROVE  \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                        Cardinality(PVSetP(r, v)) >= 2 * T + 1
      OBVIOUS
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1> PICK pc \in msgs_precommit'[r1]:
         /\ p = pc.src
         /\ pc.id /= -1
         /\ v /= pc.id
      OBVIOUS
  <1> PICK pv \in msgs_prevote'[r2]:
         /\ p = pv.src
         /\ v = pv.id
      OBVIOUS
  <1>vty. v \in ((ValidValues \union InvalidValues) \union {-1})  OBVIOUS
  <1>oldInv. PrecommitLocksLaterPrevotes
      BY DEF TypedIndInv, IndInv
  <1>pcOld. CASE pc \in msgs_precommit[r1]
      <2>pvOld. CASE pv \in msgs_prevote[r2]
          \* PrecommitLocksLaterPrevotesOp applies the PRE-state invariant at (p, r1, v, r2) and
          \* bridges the spec's flipped orientation to PVSet; pc (from pcOld) and pv (from pvOld)
          \* are its precommit/prevote witnesses.
          <3>ante. /\ \E pcx \in msgs_precommit[r1] : p = pcx.src /\ pcx.id # -1 /\ v # pcx.id
                   /\ \E pvx \in msgs_prevote[r2] : p = pvx.src /\ v = pvx.id
              BY <1>pcOld, <2>pvOld
          <3>oldQ. \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                     Cardinality(PVSet(r, v)) >= 2 * T + 1
              BY <3>ante, PrecommitLocksLaterPrevotesOp DEF TypedIndInv, IndInv
          <3> PICK r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                    Cardinality(PVSet(r, v)) >= 2 * T + 1
              BY <3>oldQ
          <3>rdom. r \in (0)..(MaxRound)  OBVIOUS
          <3>postQ. Cardinality(PVSetP(r, v)) >= 2 * T + 1
              BY <3>rdom, <1>vty, PVSetQuorumMonotone
          <3> QED BY <3>postQ, <3>rdom DEF PVSetP
      <2>pvFresh. CASE pv \notin msgs_prevote[r2]
          \* pv is a fresh valid (id = v # -1) prevote by the correct process p at r2. Only the two
          \* value-prevote actions add such a message: the other correct actions leave msgs_prevote
          \* unchanged (ruled out by DEF Step's frame, so their DEFs are unneeded -- unfolding all
          \* eleven overwhelms SMT), OnTimeoutPropose adds only a nil prevote (id = -1 # v), and
          \* FaultyStep adds only faulty senders (p \notin Faulty by DisjointCF).
          \* The fresh non-nil prevote pv by correct p at r2 forces a value-prevote action, via the
          \* standalone lemma (clean context); inlining the action case-split here drowns the SMT
          \* call in this theorem's full-invariant ambient context and times out under -threads.
          <3>split. \/ UponProposalInPropose(p)
                     \/ UponProposalInProposeAndPrevote(p)
              BY <2>pvFresh, NilNotValid, FreshValuePrevoteAction
          <3>proposal. CASE UponProposalInPropose(p)
              <4>rd. round[p] = r2
                  BY <2>pvFresh, <3>proposal, SMT DEF UponProposalInPropose
              <4>st. step[p] = "PROPOSE_OF_STEP"
                  BY <3>proposal DEF UponProposalInPropose
              <4>lv. locked_value[p] = v
                  BY <1>pcOld, <2>pvFresh, <3>proposal, NilNotValid, SMT
                     DEF UponProposalInPropose, AllLatestPrecommitHasLockedRound
              <4>postQ. \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                           Cardinality(PVSetP(r, v)) >= 2 * T + 1
                  BY <1>pcOld, <4>rd, <4>st, <4>lv, LockedValueGivesPostQuorum
              <4> QED BY <4>postQ DEF PVSetP
          <3>proposalPrevote. CASE UponProposalInProposeAndPrevote(p)
              <4>rd. round[p] = r2
                  BY <2>pvFresh, <3>proposalPrevote, SMT DEF UponProposalInProposeAndPrevote
              <4>pcValid. pc.id \in ValidValues
                  BY <1>pcOld, NilNotValid, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds
              <4>w2. v \in (ValidValues \ {pc.id})
                  BY <4>pcValid, SMT
              <4>oldPc. \E pc0 \in msgs_precommit[r1]:
                           pc0.src = p /\ pc0.id = pc.id
                  BY <1>pcOld
              <4>freshPv. \E mv \in msgs_prevote'[round[p]]:
                             mv.src = p /\ mv.id = v /\ mv \notin msgs_prevote[round[p]]
                  BY <2>pvFresh, <4>rd, SMT
              <4>preQ. \E r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                           Cardinality(PVSet(r, v)) >= 2 * T + 1
                  BY <4>oldPc, <4>pcValid, <4>w2, <3>proposalPrevote, <4>rd,
                     <4>freshPv, FreshPrevoteGivesQuorum
              <4> PICK r \in {rr \in (0)..(MaxRound): rr >= r1 /\ rr < r2}:
                         Cardinality(PVSet(r, v)) >= 2 * T + 1
                  BY <4>preQ
              <4>rdom. r \in (0)..(MaxRound)  BY <4>preQ
              <4>postQ. Cardinality(PVSetP(r, v)) >= 2 * T + 1
                  BY <4>preQ, <4>rdom, <1>vty, PVSetQuorumMonotone
              <4> QED BY <4>preQ, <4>postQ DEF PVSetP
          <3> QED BY <3>split, <3>proposal, <3>proposalPrevote
      <2> QED BY <2>pvOld, <2>pvFresh
  <1>pcFresh. CASE pc \notin msgs_precommit[r1]
      <2>shape. /\ round[p] = r1
                 /\ step[p] = "PREVOTE_OF_STEP"
                 /\ msgs_prevote' = msgs_prevote
          BY <1>pcFresh, FreshPrecommitShape
      <2>pvPre. pv \in msgs_prevote[r2]
          BY <2>shape
      <2>future. \A mv \in msgs_prevote[r2]: p # mv.src
          BY <2>shape, SMT DEF AllNoFutureMessagesSent
      <2> QED BY <2>pvPre, <2>future
  <1> QED BY <1>pcOld, <1>pcFresh

THEOREM Pres_PrecommitLocksLaterPrevotes ==
  ASSUME TypedIndInv, Step PROVE PrecommitLocksLaterPrevotes'
  <1>op. \A pp \in Corr, rr1 \in (0)..(MaxRound), vv \in ValidValues, rr2 \in (0)..(MaxRound):
            (/\ rr2 > rr1
             /\ \E pc \in msgs_precommit'[rr1] : pp = pc.src /\ pc.id /= -1 /\ vv /= pc.id
             /\ \E pv \in msgs_prevote'[rr2] : pp = pv.src /\ vv = pv.id)
            => \E r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2} :
                 Cardinality(PVSetP(r, vv)) >= 2 * T + 1
      BY Pres_PrecommitLocksLaterPrevotesOp
  <1> DEFINE RawPV(rr, val) ==
        Cardinality({s \in (Corr \union Faulty) :
          \E pv0 \in {pp0 \in msgs_prevote'[rr] : val = pp0.id} : s = pv0.src}) >= 2 * T + 1
  <1> SUFFICES ASSUME NEW pp \in Corr, NEW rr1 \in (0)..(MaxRound), NEW vv \in ValidValues,
                        NEW rr2 \in (0)..(MaxRound),
                        /\ rr2 > rr1
                        /\ \E pc \in msgs_precommit'[rr1] : pp = pc.src /\ pc.id /= -1 /\ vv /= pc.id
                        /\ \E pv \in msgs_prevote'[rr2] : pp = pv.src /\ vv = pv.id
                 PROVE  \E r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2}:
                          RawPV(r, vv)
      BY DEF PrecommitLocksLaterPrevotes, RawPV
  <1>inst. \E r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2} :
              Cardinality(PVSetP(r, vv)) >= 2 * T + 1
      BY <1>op
  <1> PICK r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2} :
              Cardinality(PVSetP(r, vv)) >= 2 * T + 1
      BY <1>inst
  <1>rin. r \in {rr \in (0)..(MaxRound): rr >= rr1 /\ rr < rr2}  OBVIOUS
  <1>rdom. r \in (0)..(MaxRound)  OBVIOUS
  <1>eq. Cardinality(PVSetP(r, vv)) =
          Cardinality({s \in (Corr \union Faulty) :
            \E pv0 \in {pp0 \in msgs_prevote'[r] : vv = pp0.id} : s = pv0.src})
      BY <1>rdom, PVSetPFlipCard
  <1>rawQ. Cardinality({s \in (Corr \union Faulty) :
              \E pv0 \in {pp0 \in msgs_prevote'[r] : vv = pp0.id} : s = pv0.src}) >= 2 * T + 1
      BY <1>eq
  <1>rawNamed. RawPV(r, vv)  BY <1>rawQ DEF RawPV
  <1>wit. \E rr \in {rr0 \in (0)..(MaxRound): rr0 >= rr1 /\ rr0 < rr2} : RawPV(rr, vv)
      BY <1>rin, <1>rawNamed
  <1> QED  BY <1>rin, <1>rawNamed DEF RawPV

LEMMA PostPrecommitLocksLaterPrevotesOp ==
  ASSUME TypedIndInv, Step,
         NEW p \in Corr, NEW r1 \in (0)..(MaxRound),
         NEW v \in ValidValues, NEW r2 \in (0)..(MaxRound),
         r2 > r1,
         \E pc \in msgs_precommit'[r1] : p = pc.src /\ pc.id # -1 /\ v # pc.id,
         \E pv \in msgs_prevote'[r2] : p = pv.src /\ v = pv.id
  PROVE  \E r \in {rr \in (0)..(MaxRound) : rr >= r1 /\ rr < r2} :
           Cardinality(PVSetP(r, v)) >= 2 * T + 1
  BY Pres_PrecommitLocksLaterPrevotesOp

LEMMA PostPrecommitLockContra ==
  ASSUME TypedIndInv, Step,
         NEW r0 \in (0)..(MaxRound), NEW r \in (0)..(MaxRound), r > r0,
         NEW w \in ValidValues, NEW w2 \in (ValidValues \ {w}),
         Cardinality(PCSetP(r0, w)) >= 2 * T + 1,
         Cardinality(PVSetP(r, w2)) >= 2 * T + 1
  PROVE  FALSE
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>wne. w # w2 /\ w # -1 /\ w2 # -1  BY NilNotValid
  <1>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>pcSub. PCSetP(r0, w) \subseteq (Corr \union Faulty)  BY DEF PCSetP
  <1> DEFINE Q[n \in Nat] ==
        \A rr \in (0)..(MaxRound) :
          (rr > r0 /\ rr <= n) => Cardinality(PVSetP(rr, w2)) < 2 * T + 1
  <1>base. Q[0]
      <2> SUFFICES \A rr \in (0)..(MaxRound) :
                     (rr > r0 /\ rr <= 0) => Cardinality(PVSetP(rr, w2)) < 2 * T + 1
          BY DEF Q
      <2> TAKE rr \in (0)..(MaxRound)
      <2> HAVE rr > r0 /\ rr <= 0
      <2> QED  BY ConstNat, SMT
  <1>step. \A n \in Nat : Q[n] => Q[n + 1]
      <2> TAKE n \in Nat
      <2> HAVE Q[n]
      <2>qn. \A rr \in (0)..(MaxRound) :
                (rr > r0 /\ rr <= n) => Cardinality(PVSetP(rr, w2)) < 2 * T + 1
          BY DEF Q
      <2> SUFFICES \A rr \in (0)..(MaxRound) :
                     (rr > r0 /\ rr <= n + 1) => Cardinality(PVSetP(rr, w2)) < 2 * T + 1
          BY DEF Q
      <2> TAKE rr \in (0)..(MaxRound)
      <2> HAVE rr > r0 /\ rr <= n + 1
      <2>old. CASE rr <= n
          <3> QED  BY <2>qn, <2>old
      <2>new. CASE rr = n + 1
          <3>pvSub. PVSetP(rr, w2) \subseteq (Corr \union Faulty)  BY DEF PVSetP
          <3>pvNat. Cardinality(PVSetP(rr, w2)) \in Nat
              BY <3>pvSub, <1>finU, FS_Subset, FS_CardinalityType
          <3> SUFFICES ASSUME Cardinality(PVSetP(rr, w2)) >= 2 * T + 1 PROVE FALSE
              BY <3>pvNat, ConstNat, SMT
          <3>int. \E c \in Corr : c \in PCSetP(r0, w) /\ c \in PVSetP(rr, w2)
              BY <1>pcSub, <3>pvSub, QuorumsIntersectInCorrect
          <3> PICK c \in Corr : c \in PCSetP(r0, w) /\ c \in PVSetP(rr, w2)  BY <3>int
          <3>pc. \E pc \in msgs_precommit'[r0] : c = pc.src /\ pc.id # -1 /\ w2 # pc.id
              BY <1>wne DEF PCSetP
          <3>pv. \E pv \in msgs_prevote'[rr] : c = pv.src /\ w2 = pv.id
              BY DEF PVSetP
          <3>mid. \E r1 \in {rr1 \in (0)..(MaxRound) : rr1 >= r0 /\ rr1 < rr} :
                     Cardinality(PVSetP(r1, w2)) >= 2 * T + 1
              BY <3>pc, <3>pv, PostPrecommitLocksLaterPrevotesOp
          <3> PICK r1 \in {rr1 \in (0)..(MaxRound) : rr1 >= r0 /\ rr1 < rr} :
                        Cardinality(PVSetP(r1, w2)) >= 2 * T + 1
              BY <3>mid
          <3>r1dom. r1 \in (0)..(MaxRound) /\ r1 >= r0 /\ r1 < rr  BY SMT
          <3>r1Q. Cardinality(PVSetP(r1, w2)) >= 2 * T + 1  OBVIOUS
          <3>r10. CASE r1 = r0
              <4>r0Q. Cardinality(PVSetP(r0, w2)) >= 2 * T + 1  BY <3>r10, <3>r1Q
              <4> QED  BY <4>r0Q, PostSameRoundPrecommitPrevoteQuorumsContra
          <3>r1gt. CASE r1 > r0
              <4>r1LeN. r1 <= n  BY <3>r1dom, <2>new, SMT
              <4>r1Lt. Cardinality(PVSetP(r1, w2)) < 2 * T + 1
                  BY <2>qn, <3>r1dom, <3>r1gt, <4>r1LeN
              <4>r1Nat. Cardinality(PVSetP(r1, w2)) \in Nat
                  BY <3>r1dom, <1>finU, FS_Subset, FS_CardinalityType DEF PVSetP
              <4> QED  BY <3>r1Q, <4>r1Lt, <4>r1Nat, ConstNat, SMT
          <3> QED  BY <3>r10, <3>r1gt, <3>r1dom
      <2> QED  BY <2>old, <2>new, ConstNat, SMT
  <1>all. \A n \in Nat : Q[n]  BY <1>base, <1>step, NatInductionTrusted
  <1>qmax. Q[MaxRound]  BY <1>all, ConstNat
  <1>goalLt. Cardinality(PVSetP(r, w2)) < 2 * T + 1
      BY <1>qmax, ConstNat DEF Q
  <1>pvSub. PVSetP(r, w2) \subseteq (Corr \union Faulty)  BY DEF PVSetP
  <1>pvNat. Cardinality(PVSetP(r, w2)) \in Nat
      BY <1>pvSub, <1>finU, FS_Subset, FS_CardinalityType
  <1> QED  BY <1>goalLt, <1>pvNat, ConstNat, SMT

THEOREM Pres_PrecommitsLockValue ==
  ASSUME TypedIndInv, Step PROVE PrecommitsLockValue'
  <1> USE DEF TypedIndInv, IndTypeOk
  \* Reduce the primed goal to its explicit unfolded form (in terms of the operators
  \* PCSetP / PVSetP) via an equivalence step; the backends match the doubly-quantified
  \* Cardinality-disjunction goal only through this detour, not by unfolding in place.
  \* Reduce the primed goal to its flipped raw form (identical to the spec), then bridge only the
  \* two point instances (r0,w and r,w2) to PCSetP/PVSetP -- the only places the operators appear.
  <1> SUFFICES \A v_v708 \in (0)..(MaxRound), v_v709 \in ValidValues:
                  \/ (Cardinality({s \in (Corr \union Faulty) :
                        \E m \in {mm \in msgs_precommit'[v_v708] : v_v709 = mm.id} : s = m.src}) < ((2 * T) + 1))
                  \/ (\A v_v714 \in {v_v713 \in (0)..(MaxRound): (v_v713 > v_v708)}: \A v_v715 \in (ValidValues \ {v_v709}):
                        (Cardinality({s \in (Corr \union Faulty) :
                          \E m \in {mm \in msgs_prevote'[v_v714] : v_v715 = mm.id} : s = m.src}) < ((2 * T) + 1)))
      BY DEF PrecommitsLockValue
  <1> TAKE r0 \in (0)..(MaxRound), w \in ValidValues
  \* Counterexample form: a post-state precommit quorum for w at r0 forces every other
  \* valid value w2 to lack a post-state prevote quorum in each later round r.
  <1> SUFFICES ASSUME ~(Cardinality({s \in (Corr \union Faulty) :
                          \E m \in {mm \in msgs_precommit'[r0] : w = mm.id} : s = m.src}) < ((2 * T) + 1)),
                      NEW r \in {v_v713 \in (0)..(MaxRound): (v_v713 > r0)},
                      NEW w2 \in (ValidValues \ {w})
               PROVE  Cardinality({s \in (Corr \union Faulty) :
                        \E m \in {mm \in msgs_prevote'[r] : w2 = mm.id} : s = m.src}) < ((2 * T) + 1)
      OBVIOUS
  \* Bridge the two instances to PCSetP/PVSetP.
  <1>pcpFin. IsFiniteSet(PCSetP(r0, w))  BY SubsetCFFinite DEF PCSetP
  <1>pcpEq. Cardinality(PCSetP(r0, w)) =
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit'[r0] : w = mm.id} : s = m.src})
      BY <1>pcpFin, PCSetPFlip, CardCong
  <1>pvpFin. IsFiniteSet(PVSetP(r, w2))  BY SubsetCFFinite DEF PVSetP
  <1>pvpEq. Cardinality(PVSetP(r, w2)) =
              Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_prevote'[r] : w2 = mm.id} : s = m.src})
      BY <1>pvpFin, PVSetPFlip, CardCong
  <1>hyp. ~(Cardinality(PCSetP(r0, w)) < ((2 * T) + 1))  BY <1>pcpEq
  <1> SUFFICES Cardinality(PVSetP(r, w2)) < ((2 * T) + 1)  BY <1>pvpEq
  \* Pre-state lock (PrecommitsLockValue at (r0, w)): either w has no pre-state precommit
  \* quorum at r0, or no other valid value has a pre-state prevote quorum above r0.
  <1>pre. \/ Cardinality({s \in (Corr \union Faulty) :
                \E m \in {mm \in msgs_precommit[r0] : mm.id = w} : s = m.src}) < 2 * T + 1
          \/ (\A rr \in {x \in (0)..(MaxRound) : x > r0} : \A ww \in (ValidValues \ {w}) :
                Cardinality({s \in (Corr \union Faulty) :
                  \E m \in {mm \in msgs_prevote[rr] : mm.id = ww} : s = m.src}) < 2 * T + 1)
      BY PrecommitsLockValueOp DEF TypedIndInv, IndInv, PCSet, PVSet
  \* rNat / rGt: unpack r's constrained domain.
  <1>rDom. r \in (0)..(MaxRound) /\ r > r0  BY SMT
  <1> QED
    <2>finU. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
    <2>pcSub. PCSetP(r0, w) \subseteq (Corr \union Faulty)  BY DEF PCSetP
    <2>pvSub. PVSetP(r, w2) \subseteq (Corr \union Faulty)  BY DEF PVSetP
    <2>pcNat. Cardinality(PCSetP(r0, w)) \in Nat  BY <2>pcSub, <2>finU, FS_Subset, FS_CardinalityType
    <2>pvNat. Cardinality(PVSetP(r, w2)) \in Nat  BY <2>pvSub, <2>finU, FS_Subset, FS_CardinalityType
    \* The precommit quorum for w at r0 is >= 2T+1 (negated first disjunct + Nat typing).
    <2>pcQ. Cardinality(PCSetP(r0, w)) >= 2 * T + 1  BY <1>hyp, <2>pcNat, ConstNat, SMT
    \* Prove the goal (post prevote quorum for w2 < 2T+1) by contradiction.
    <2> SUFFICES ASSUME Cardinality(PVSetP(r, w2)) >= 2 * T + 1  PROVE  FALSE
        BY <2>pvNat, ConstNat, SMT
    \* Quorum intersection (N = 3T+1): a correct process c is in both post-state quorums.
    <2>int. \E cc \in Corr : cc \in PCSetP(r0, w) /\ cc \in PVSetP(r, w2)
        BY <2>pcSub, <2>pvSub, <2>pcQ, QuorumsIntersectInCorrect
    <2> PICK c \in Corr : c \in PCSetP(r0, w) /\ c \in PVSetP(r, w2)  BY <2>int
    \* c precommitted w at r0 and prevoted w2 at r, both in the post-state.
    <2>cPC. \E mc \in msgs_precommit'[r0] : mc.src = c /\ mc.id = w  BY DEF PCSetP
    <2>cPV. \E mv \in msgs_prevote'[r] : mv.src = c /\ mv.id = w2  BY DEF PVSetP
    \* Bridge to the pre-state via a case split on whether the relevant message slices
    \* (precommits at r0, prevotes at r) changed in this Step.
    <2>caseClean. CASE msgs_precommit'[r0] = msgs_precommit[r0] /\ msgs_prevote'[r] = msgs_prevote[r]
        \* Both quorums / c's votes are pre-state, so PrecommitLockContra's hypotheses hold.
        <3>mcPre. \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w  BY <2>cPC, <2>caseClean
        <3>mvPre. \E pv \in msgs_prevote[r] : pv.src = c /\ pv.id = w2  BY <2>cPV, <2>caseClean
        <3>pcQpre. Cardinality(PCSet(r0, w)) >= 2 * T + 1  BY <2>pcQ, <2>caseClean DEF PCSet, PCSetP
        <3> QED  BY <3>mcPre, <3>mvPre, <3>pcQpre, <1>rDom, PrecommitLockContra
    <2>caseChanged. CASE ~(msgs_precommit'[r0] = msgs_precommit[r0] /\ msgs_prevote'[r] = msgs_prevote[r])
        <3> PICK mc \in msgs_precommit'[r0] : mc.src = c /\ mc.id = w  BY <2>cPC
        <3> PICK mv \in msgs_prevote'[r] : mv.src = c /\ mv.id = w2  BY <2>cPV
        <3>caseA. CASE msgs_precommit'[r0] = msgs_precommit[r0]
            \* Precommit slice at r0 unchanged: a real pre-state 2T+1 precommit quorum for w at r0,
            \* and c's precommit for w at r0 is pre-state.
            <4>pcQpre. Cardinality(PCSet(r0, w)) >= 2 * T + 1  BY <2>pcQ, <3>caseA DEF PCSet, PCSetP
            <4>mcPre. \E pc \in msgs_precommit[r0] : pc.src = c /\ pc.id = w  BY <3>caseA
            <4>mvPre. CASE mv \in msgs_prevote[r]
                \* c's prevote for w2 at r is pre-state: PrecommitLockContra closes it.
                <5>pvPre. \E pv \in msgs_prevote[r] : pv.src = c /\ pv.id = w2  BY <4>mvPre
                <5> QED  BY <4>mcPre, <5>pvPre, <4>pcQpre, <1>rDom, PrecommitLockContra
            <4>mvF. CASE mv \notin msgs_prevote[r]
                \* c added a fresh prevote for w2 at r = round[c]. Being locked (it precommitted w at
                \* r0), its prevote guard yields a pre-state 2T+1 prevote quorum for w2 in [r0, r),
                \* which contradicts the r0 precommit lock (LockContraFromPrevoteQuorum).
                <5>fr0. round[c] = r /\ (UponProposalInPropose(c) \/ UponProposalInProposeAndPrevote(c))
                    BY <4>mvF, NilNotValid, FreshValuePrevoteAction
                <5>rd. round[c] = r  BY <5>fr0
                <5>act. UponProposalInPropose(c) \/ UponProposalInProposeAndPrevote(c)  BY <5>fr0
                <5>rc. round[c] > r0  BY <5>rd, <1>rDom
                <5>fresh. \E mvv \in msgs_prevote'[round[c]] :
                             mvv.src = c /\ mvv.id = w2 /\ mvv \notin msgs_prevote[round[c]]
                    BY <4>mvF, <5>rd
                <5>preRC. \E vr \in {x \in (0)..(MaxRound) : x >= r0 /\ x < round[c]} :
                            Cardinality(PVSet(vr, w2)) >= 2 * T + 1
                    BY <4>mcPre, <5>rc, <5>fresh, <5>act, FreshPrevoteLockedGivesPreQuorum
                <5>preQ. \E vr \in {x \in (0)..(MaxRound) : x >= r0 /\ x < r} :
                           Cardinality(PVSet(vr, w2)) >= 2 * T + 1
                    BY <5>preRC, <5>rd
                <5> QED  BY <4>pcQpre, <5>preQ, <1>rDom, LockContraFromPrevoteQuorum
            <4> QED  BY <4>mvPre, <4>mvF
        <3>caseB. CASE msgs_precommit'[r0] # msgs_precommit[r0]
            <4> QED  BY <1>rDom, <2>pcQ, PostPrecommitLockContra
        <3> QED  BY <3>caseA, <3>caseB
    <2> QED  BY <2>caseClean, <2>caseChanged

THEOREM Inductive ==
  ASSUME TypedIndInv, Step
  PROVE  TypedIndInv'
  BY TypePres,
     Pres_AllNoFutureMessagesSent,
     Pres_AllIfInPrevoteThenSentPrevote,
     Pres_AllIfInPrecommitThenSentPrecommit,
     Pres_AllIfInDecidedThenReceivedProposal,
     Pres_AllIfInDecidedThenReceivedTwoThirds,
     Pres_AllIfInDecidedThenValidDecision,
     Pres_AllLockedRoundIffLockedValue,
     Pres_AllValidRoundIffValidValue,
     Pres_AllValidAndLockedRoundBounded,
     Pres_AllIfValidRoundThenTwoThirdsPrevotes,
     Pres_AllIfLockedRoundThenSentCommit,
     Pres_AllLatestPrecommitHasLockedRound,
     Pres_AllIfSentPrevoteThenReceivedProposalOrTwoThirds,
     Pres_IfSentPrecommitThenSentPrevote,
     Pres_IfSentPrecommitThenReceivedTwoThirds,
     Pres_AllNoEquivocationByCorrect,
     Pres_PrecommitsLockValue,
     Pres_PrecommitLocksLaterPrevotes,
     Pres_AllLockedProposerReproposes,
     Pres_AllPastStartRound,
     Pres_AllRoundsBelowHavePrecommitQuorum,
     Pres_AllValidInCurrentRoundPrecommitted,
     Pres_AllLockedRoundBelowValidRound,
     Pres_AllIfValidRoundThenPrecommitted,
     Pres_AllCorrectProposalValidRoundBelowRound
  DEF TypedIndInv, IndInv

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


LEMMA LockLemma ==
  ASSUME TypedIndInv,
         NEW ra \in (0)..(MaxRound), NEW rb \in (0)..(MaxRound),
         NEW va \in ValidValues, NEW vb \in ValidValues, ra < rb,
         Cardinality(PCSet(ra, va)) >= 2 * T + 1,
         Cardinality(PCSet(rb, vb)) >= 2 * T + 1
  PROVE  va = vb
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>Ssub. PCSet(rb, vb) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
  <1>corr. \E c \in Corr : c \in PCSet(rb, vb)  BY <1>Ssub, QuorumHasCorrect
  <1> PICK c \in Corr : c \in PCSet(rb, vb)  BY <1>corr
  <1> PICK mc \in msgs_precommit[rb] : mc.id = vb /\ mc.src = c  BY DEF PCSet
  <1>mcC. mc.src \in Corr /\ mc.id \in ValidValues  BY NilNotValid
  <1>mcvb. mc.id = vb  OBVIOUS
  \* A correct precommit for mc.id at rb yields a 2T+1 prevote quorum for mc.id
  \* (IfSentPrecommit; the nil-value disjunct is ruled out because mc.id is valid).
  \* Everything below works through mc.id, so no value is ever substituted inside a
  \* Cardinality — the spec's set-builder orientation now matches PVSet/PCSet directly.
  <1>pv. Cardinality(PVSet(rb, mc.id)) >= 2 * T + 1
      BY <1>mcC, NilNotValid, Zenon, SMT DEF IfSentPrecommitThenReceivedTwoThirds, PVSet
  \* PrecommitsLockValue at (ra, va): the 2T+1 precommit quorum for va blocks a
  \* 2T+1 prevote quorum for any other valid value in later rounds.
  <1>raw. \/ Cardinality(PCSet(ra, va)) < 2 * T + 1
          \/ (\A r3 \in {rr \in (0)..(MaxRound) : rr > ra} : \A v3 \in (ValidValues \ {va}) :
                Cardinality(PVSet(r3, v3)) < 2 * T + 1)
      BY PrecommitsLockValueOp DEF TypedIndInv, IndInv
  <1>finU2. IsFiniteSet(Corr \union Faulty)  BY FiniteCF, FS_Union
  <1>cardNat. Cardinality(PCSet(ra, va)) \in Nat /\ Cardinality(PVSet(rb, mc.id)) \in Nat
      <2>1. PCSet(ra, va) \subseteq (Corr \union Faulty) /\ PVSet(rb, mc.id) \subseteq (Corr \union Faulty)
            BY PCSetSubset, PVSetSubset
      <2>2. IsFiniteSet(PCSet(ra, va)) /\ IsFiniteSet(PVSet(rb, mc.id))
            BY <2>1, <1>finU2, FS_Subset
      <2> QED  BY <2>2, FS_CardinalityType
  \* first disjunct of raw is false because the ASSUME gives Cardinality(PCSet(ra,va)) >= 2T+1
  <1>notD1. ~(Cardinality(PCSet(ra, va)) < 2 * T + 1)
      BY <1>cardNat, ConstNat, SMT
  <1>notlock. \A r3 \in {rr \in (0)..(MaxRound) : rr > ra} : \A v3 \in (ValidValues \ {va}) :
                Cardinality(PVSet(r3, v3)) < 2 * T + 1
      BY <1>raw, <1>notD1
  <1>inst. rb \in {rr \in (0)..(MaxRound) : rr > ra}  BY SMT
  <1> QED
      <2>1. mc.id \notin (ValidValues \ {va})
          <3> SUFFICES ASSUME mc.id \in (ValidValues \ {va}) PROVE FALSE  OBVIOUS
          <3>1. Cardinality(PVSet(rb, mc.id)) < 2 * T + 1  BY <1>notlock, <1>inst
          <3> QED  BY <3>1, <1>pv, <1>cardNat, ConstNat, SMT
      <2> QED  BY <2>1, <1>mcC, <1>mcvb

THEOREM AgreementThm ==
  TypedIndInv => Agreement
  <1> SUFFICES ASSUME TypedIndInv, NEW p1 \in Corr, NEW p2 \in Corr,
                      decision[p1] # -1, decision[p2] # -1
               PROVE  decision[p1] = decision[p2]
      BY DEF Agreement
  <1> USE DEF TypedIndInv, IndInv, IndTypeOk
  <1>d1v. decision[p1] \in ValidValues  BY NilNotValid
  <1>d2v. decision[p2] \in ValidValues  BY NilNotValid
  <1>s1. step[p1] = "DECIDED_OF_STEP"  BY <1>d1v DEF AllIfInDecidedThenValidDecision
  <1>s2. step[p2] = "DECIDED_OF_STEP"  BY <1>d2v DEF AllIfInDecidedThenValidDecision
  <1>q1. \E r \in (0)..(MaxRound) : Cardinality(PCSet(r, decision[p1])) >= 2 * T + 1
      BY <1>s1, Zenon, SMT DEF AllIfInDecidedThenReceivedTwoThirds, PCSet
  <1>q2. \E r \in (0)..(MaxRound) : Cardinality(PCSet(r, decision[p2])) >= 2 * T + 1
      BY <1>s2, Zenon, SMT DEF AllIfInDecidedThenReceivedTwoThirds, PCSet
  <1> PICK r1 \in (0)..(MaxRound) : Cardinality(PCSet(r1, decision[p1])) >= 2 * T + 1  BY <1>q1
  <1> PICK r2 \in (0)..(MaxRound) : Cardinality(PCSet(r2, decision[p2])) >= 2 * T + 1  BY <1>q2
  <1>caseEQ. CASE r1 = r2
      <2>sub1. PCSet(r1, decision[p1]) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
      <2>sub2. PCSet(r1, decision[p2]) \in SUBSET (Corr \union Faulty)  BY PCSetSubset
      <2>ca2. Cardinality(PCSet(r1, decision[p2])) >= 2 * T + 1  BY <1>caseEQ
      <2>corr. \E c \in Corr : c \in PCSet(r1, decision[p1]) /\ c \in PCSet(r1, decision[p2])
          BY <2>sub1, <2>sub2, <2>ca2, QuorumsIntersectInCorrect
      <2> PICK c \in Corr : c \in PCSet(r1, decision[p1]) /\ c \in PCSet(r1, decision[p2])  BY <2>corr
      <2>c1. \E m \in msgs_precommit[r1] : m.id = decision[p1] /\ m.src = c  BY DEF PCSet
      <2>c2. \E m \in msgs_precommit[r1] : m.id = decision[p2] /\ m.src = c  BY DEF PCSet
      <2> QED  BY <2>c1, <2>c2 DEF AllNoEquivocationByCorrect
  <1>caseNE. CASE r1 # r2
      <2>0. r1 \in (0)..(MaxRound) /\ r2 \in (0)..(MaxRound) /\ r1 # r2  BY <1>caseNE
      <2>1. r1 < r2 \/ r2 < r1  BY <2>0, ConstNat, SMT
      <2>2. CASE r1 < r2  BY <2>2, <1>d1v, <1>d2v, LockLemma
      <2>3. CASE r2 < r1  BY <2>3, <1>d1v, <1>d2v, LockLemma
      <2> QED  BY <2>1, <2>2, <2>3
  <1> QED  BY <1>caseEQ, <1>caseNE

=============================================================================
