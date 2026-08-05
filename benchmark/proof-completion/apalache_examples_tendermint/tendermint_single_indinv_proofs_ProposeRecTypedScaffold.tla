------------------- MODULE tendermint_single_indinv_proofs_ProposeRecTypedScaffold -------------------

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
=============================================================================
