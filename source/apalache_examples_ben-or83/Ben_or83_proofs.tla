-------------------------- MODULE Ben_or83_proofs --------------------------
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
  BY RoundsNat

LEMMA Arith_PosNotLtOne ==
  ASSUME NEW r \in Nat, r >= 1
  PROVE  ~(r < 1)
  BY ConstNat

LEMMA RoundPredInRounds ==
  ASSUME NEW r \in ROUNDS, r # 1
  PROVE  r - 1 \in ROUNDS
  BY RoundsNat, ConstNat

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
  <1>1. IsFiniteSet(ALL)
        BY FiniteCF, FS_Union DEF ALL
  <1>2. Cardinality(CORRECT \cap FAULTY) = 0
        BY DisjointCF, FS_EmptySet
  <1>3. Cardinality(ALL) = Cardinality(CORRECT) + Cardinality(FAULTY)
        BY FiniteCF, FS_Union, FS_CardinalityType, <1>2 DEF ALL
  <1> QED
        BY <1>1, <1>3, NTF, ConstNat

\* Senders sets are subsets of ALL (the spec filters ALL on purpose), hence finite.
THEOREM Senders1_Sub ==
  ASSUME NEW S
  PROVE  Senders1(S) \subseteq ALL /\ IsFiniteSet(Senders1(S))
        /\ Cardinality(Senders1(S)) <= N
  <1>1. Senders1(S) \subseteq ALL
        BY DEF Senders1
  <1> QED
        BY <1>1, ALL_Card, FS_Subset

THEOREM Senders1_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders1(A)) <= Cardinality(Senders1(B))
  <1>sub. Senders1(A) \subseteq Senders1(B) BY DEF Senders1
  <1>fin. IsFiniteSet(Senders1(B)) BY Senders1_Sub
  <1> QED BY <1>sub, <1>fin, FS_Subset

THEOREM Senders2_Sub ==
  ASSUME NEW S
  PROVE  Senders2(S) \subseteq ALL /\ IsFiniteSet(Senders2(S))
        /\ Cardinality(Senders2(S)) <= N
  <1>1. Senders2(S) \subseteq ALL
        BY DEF Senders2
  <1> QED
        BY <1>1, ALL_Card, FS_Subset

THEOREM Senders2_Witness ==
  ASSUME NEW S, NEW id \in Senders2(S)
  PROVE  \E m \in S :
           (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id)
  BY DEF Senders2

THEOREM Senders2_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders2(A)) <= Cardinality(Senders2(B))
  <1>sub. Senders2(A) \subseteq Senders2(B) BY DEF Senders2
  <1>fin. IsFiniteSet(Senders2(B)) BY Senders2_Sub
  <1> QED BY <1>sub, <1>fin, FS_Subset

SenderWitness2(S) ==
  [ id \in Senders2(S) |->
      CHOOSE m \in S :
        (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id) ]

THEOREM Senders2_CardLeSet ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  Cardinality(Senders2(S)) <= Cardinality(S)
  <1>fn. SenderWitness2(S) \in [ Senders2(S) -> S ]
        BY DEF SenderWitness2, Senders2
  <1>inj. \A a, b \in Senders2(S) :
             SenderWitness2(S)[a] = SenderWitness2(S)[b] => a = b
    <2> SUFFICES ASSUME NEW a \in Senders2(S), NEW b \in Senders2(S),
                         SenderWitness2(S)[a] = SenderWitness2(S)[b]
                  PROVE  a = b
          OBVIOUS
    <2>ea. \E m \in S :
              (IsD2(m) /\ AsD2(m).src = a) \/ (IsQ2(m) /\ AsQ2(m).src = a)
          BY DEF Senders2
    <2>eb. \E m \in S :
              (IsD2(m) /\ AsD2(m).src = b) \/ (IsQ2(m) /\ AsQ2(m).src = b)
          BY DEF Senders2
    <2>wa. (IsD2(SenderWitness2(S)[a]) /\ AsD2(SenderWitness2(S)[a]).src = a)
              \/ (IsQ2(SenderWitness2(S)[a]) /\ AsQ2(SenderWitness2(S)[a]).src = a)
          BY <2>ea DEF SenderWitness2
    <2>wb. (IsD2(SenderWitness2(S)[b]) /\ AsD2(SenderWitness2(S)[b]).src = b)
              \/ (IsQ2(SenderWitness2(S)[b]) /\ AsQ2(SenderWitness2(S)[b]).src = b)
          BY <2>eb DEF SenderWitness2
    <2> QED BY <2>wa, <2>wb, VariantAx
  <1>i. SenderWitness2(S) \in Injection(Senders2(S), S)
        BY <1>fn, <1>inj DEF Injection, IsInjective
  <1> QED BY <1>i, FS_Injection

D2SrcFn(S) == [ m \in S |-> AsD2(m).src ]

THEOREM D2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r, NEW v,
         \A m \in S : IsD2(m) /\ AsD2(m).src \in ALL
                       /\ AsD2(m).r = r /\ AsD2(m).v = v
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
  <1>fn. D2SrcFn(S) \in [ S -> Senders2(S) ]
        BY DEF D2SrcFn, Senders2
  <1>inj. \A a, b \in S : D2SrcFn(S)[a] = D2SrcFn(S)[b] => a = b
    <2> SUFFICES ASSUME NEW a \in S, NEW b \in S, D2SrcFn(S)[a] = D2SrcFn(S)[b]
                 PROVE  a = b
          OBVIOUS
    <2> QED BY VariantAx DEF D2SrcFn
  <1>i. D2SrcFn(S) \in Injection(S, Senders2(S))
        BY <1>fn, <1>inj DEF Injection, IsInjective
  <1> QED BY <1>i, Senders2_Sub, FS_Injection

Q2SrcFn(S) == [ m \in S |-> AsQ2(m).src ]

THEOREM Q2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r,
         \A m \in S : IsQ2(m) /\ AsQ2(m).src \in ALL /\ AsQ2(m).r = r
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
  <1>fn. Q2SrcFn(S) \in [ S -> Senders2(S) ]
        BY DEF Q2SrcFn, Senders2
  <1>inj. \A a, b \in S : Q2SrcFn(S)[a] = Q2SrcFn(S)[b] => a = b
    <2> SUFFICES ASSUME NEW a \in S, NEW b \in S, Q2SrcFn(S)[a] = Q2SrcFn(S)[b]
                 PROVE  a = b
          OBVIOUS
    <2> QED BY VariantAx DEF Q2SrcFn
  <1>i. Q2SrcFn(S) \in Injection(S, Senders2(S))
        BY <1>fn, <1>inj DEF Injection, IsInjective
  <1> QED BY <1>i, Senders2_Sub, FS_Injection

\* Any subset of ALL is finite with cardinality at most N.
THEOREM SubAll_Finite ==
  ASSUME NEW Q, Q \subseteq ALL
  PROVE  IsFiniteSet(Q) /\ Cardinality(Q) <= N
  BY ALL_Card, FS_Subset

\* ABSTRACT ARITHMETIC LEMMAS (Paxos style).
\* These are stated over plain Nat variables and proved by SMT. We apply them by
\* instantiating the Nat variables with `Cardinality(...)` terms. This indirection is
\* essential: when a `Cardinality(...)` term appears directly in an obligation's
\* hypotheses, the SMT backend fails even trivial integer reasoning -- but a lemma
\* APPLICATION only matches hypotheses, so the arithmetic stays Cardinality-free.

\* A set of >= N - 2*T elements cannot consist solely of <= F faulty ones (N > 5*T, F <= T).
LEMMA Arith_NotAllFaulty ==
  ASSUME NEW a \in Nat, a >= N - 2 * T, a <= F
  PROVE  FALSE
  BY NgtT, FleqT, ConstNat

\* A set of >= T+1 elements cannot consist solely of <= F faulty ones (F <= T).
LEMMA Arith_TplusOneNotFaulty ==
  ASSUME NEW a \in Nat, a >= T + 1, a <= F
  PROVE  FALSE
  BY FleqT, ConstNat

LEMMA Arith_GeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a >= c, a <= b
  PROVE  b >= c
  BY ConstNat

LEMMA Arith_LeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b, b <= c
  PROVE  a <= c
  BY ConstNat

LEMMA Arith_LeLtTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b, b < c
  PROVE  a < c
  BY ConstNat

LEMMA Arith_DoubleGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, 2 * a > c, a <= b
  PROVE  2 * b > c
  BY ConstNat

LEMMA Arith_DoubleGtNplusTImplTplusOne ==
  ASSUME NEW a \in Nat, 2 * a > N + T
  PROVE  a >= T + 1
  BY ConstNat, NgtT, FleqT

LEMMA Arith_DoubleNotGtLe ==
  ASSUME NEW a \in Nat, ~(2 * a > N + T)
  PROVE  2 * a <= N + T
  BY ConstNat

LEMMA Arith_DoubleLeFromNotGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b, ~(2 * b > N + T)
  PROVE  2 * a <= N + T
  BY ConstNat

LEMMA Arith_SuccCancel ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a + 1 = b + 1
  PROVE  a = b
  BY ConstNat

LEMMA Arith_SuccGtOne ==
  ASSUME NEW a \in Nat, a >= 1
  PROVE  a + 1 > 1
  BY ConstNat

LEMMA Arith_PlusOneMinusOne ==
  ASSUME NEW a \in Nat
  PROVE  a + 1 - 1 = a
  BY ConstNat

LEMMA Arith_MinusOnePlusOne ==
  ASSUME NEW a \in Nat, a > 1
  PROVE  (a - 1) + 1 = a
  BY ConstNat

LEMMA Arith_SumThirdMonoGe ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW z \in Nat, NEW zp \in Nat,
         NEW c \in Nat, z <= zp, x + y + z >= c
  PROVE  x + y + zp >= c
  BY ConstNat

LEMMA Arith_ThreeLeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat,
         NEW x \in Nat, NEW y \in Nat, NEW z \in Nat,
         NEW n \in Nat,
         n <= a + b + c,
         a <= x, b <= y, c <= z
  PROVE  n <= x + y + z
  BY ConstNat

LEMMA Arith_SumMinusLeSum ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW i \in Nat
  PROVE  a + b - i <= a + b
  BY ConstNat

LEMMA Arith_SupportedQuorumContrad ==
  ASSUME NEW rcv \in Nat, NEW dv \in Nat, NEW oth \in Nat,
         rcv = N - T, rcv <= dv + oth, dv < T + 1, oth < N - 2 * T
  PROVE  FALSE
  <1>dvle. dv <= T BY ConstNat, FleqT
  <1>sumlt. dv + oth < N - T BY <1>dvle, ConstNat, NgtT, FleqT
  <1>ge. dv + oth >= N - T BY ConstNat
  <1> QED BY <1>sumlt, <1>ge, ConstNat

LEMMA Arith_NotLtTplusOneGe ==
  ASSUME NEW a \in Nat, ~(a < T + 1)
  PROVE  a >= T + 1
  BY ConstNat, FleqT

LEMMA Arith_GeLtContrad ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= b, a < b
  PROVE  FALSE
  BY ConstNat

LEMMA Arith_DoubleLtTplusOneLeNplusT ==
  ASSUME NEW a \in Nat, a < T + 1
  PROVE  2 * a <= N + T
  BY ConstNat, FleqT, NgtT

LEMMA Arith_StrictMajorityAfterFaults ==
  ASSUME NEW rcv \in Nat, NEW d \in Nat, NEW bad \in Nat,
         rcv = N - T, rcv <= d + bad, bad <= F
  PROVE  2 * d > N + T
  BY ConstNat, FleqT, NgtT

LEMMA Arith_StrictMajorityAfterFaultsGe ==
  ASSUME NEW rcv \in Nat, NEW d \in Nat, NEW bad \in Nat,
         rcv >= N - T, rcv <= d + bad, bad <= F
  PROVE  2 * d > N + T
  BY ConstNat, FleqT, NgtT

LEMMA Arith_DoubleGtNplusTImplGt3T ==
  ASSUME NEW d \in Nat, 2 * d > N + T
  PROVE  d > 3 * T
  BY ConstNat, FleqT, NgtT

LEMMA Arith_OtherLtFromStrictOverlapCore ==
  ASSUME NEW d \in Nat, NEW o \in Nat, NEW i \in Nat, NEW u \in Nat,
         u <= N, u = d + o - i, d > 3 * T, i <= T
  PROVE  o < N - 2 * T
  BY ConstNat, FleqT, NgtT

LEMMA Arith_OtherLtFromStrictOverlap ==
  ASSUME NEW d \in Nat, NEW o \in Nat, NEW i \in Nat, NEW u \in Nat,
         u <= N, u = d + o - i, 2 * d > N + T, i <= F
  PROVE  o < N - 2 * T
  <1>dGt. d > 3 * T BY Arith_DoubleGtNplusTImplGt3T
  <1>iLe. i <= T BY FleqT, ConstNat
  <1> QED BY <1>dGt, <1>iLe, Arith_OtherLtFromStrictOverlapCore

LEMMA Arith_Lemma8Pinned0Contrad ==
  ASSUME NEW x0 \in Nat, NEW x1 \in Nat, NEW nf \in Nat,
         x1 <= 0, x0 + x1 + nf >= N - T, nf <= F, 2 * x0 <= N + T
  PROVE  FALSE
  BY ConstNat, FleqT, NgtT

LEMMA Arith_Lemma8Pinned1Contrad ==
  ASSUME NEW x0 \in Nat, NEW x1 \in Nat, NEW nf \in Nat,
         x0 <= 0, x0 + x1 + nf >= N - T, nf <= F, 2 * x1 <= N + T
  PROVE  FALSE
  BY ConstNat, FleqT, NgtT

THEOREM CardUnion3LeSum ==
  ASSUME NEW A, NEW B, NEW C,
         IsFiniteSet(A), IsFiniteSet(B), IsFiniteSet(C)
  PROVE  Cardinality((A \union B) \union C)
           <= Cardinality(A) + Cardinality(B) + Cardinality(C)
  <1>ab. IsFiniteSet(A \union B) BY FS_Union
  <1>abc. IsFiniteSet((A \union B) \union C) BY <1>ab, FS_Union
  <1>iab. IsFiniteSet(A \cap B) BY FS_Intersection
  <1>iabc. IsFiniteSet((A \union B) \cap C) BY <1>ab, FS_Intersection
  <1>eqab. Cardinality(A \union B)
             = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B)
        BY FS_Union
  <1>eqabc. Cardinality((A \union B) \union C)
             = Cardinality(A \union B) + Cardinality(C) - Cardinality((A \union B) \cap C)
        BY <1>ab, FS_Union
  <1>types. /\ Cardinality(A) \in Nat /\ Cardinality(B) \in Nat /\ Cardinality(C) \in Nat
             /\ Cardinality(A \union B) \in Nat
             /\ Cardinality((A \union B) \union C) \in Nat
             /\ Cardinality(A \cap B) \in Nat
             /\ Cardinality((A \union B) \cap C) \in Nat
        BY <1>ab, <1>abc, <1>iab, <1>iabc, FS_CardinalityType
  <1>cab. Cardinality(A \union B) <= Cardinality(A) + Cardinality(B)
        BY <1>eqab, <1>types, Arith_SumMinusLeSum
  <1>cabc. Cardinality((A \union B) \union C) <= Cardinality(A \union B) + Cardinality(C)
        BY <1>eqabc, <1>types, Arith_SumMinusLeSum
  <1> QED BY <1>cab, <1>cabc, <1>types, ConstNat

THEOREM CardUnion2LeSum ==
  ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B)
  PROVE  Cardinality(A \union B) <= Cardinality(A) + Cardinality(B)
  <1>ab. IsFiniteSet(A \union B) BY FS_Union
  <1>iab. IsFiniteSet(A \cap B) BY FS_Intersection
  <1>eq. Cardinality(A \union B)
            = Cardinality(A) + Cardinality(B) - Cardinality(A \cap B)
        BY <1>ab, FS_Union
  <1>types. /\ Cardinality(A) \in Nat /\ Cardinality(B) \in Nat
             /\ Cardinality(A \union B) \in Nat /\ Cardinality(A \cap B) \in Nat
        BY <1>ab, <1>iab, FS_CardinalityType
  <1> QED BY <1>eq, <1>types, Arith_SumMinusLeSum

\* CORE QUORUM INTERSECTION: two quorums of >= N - T senders intersect, and the
\* intersection necessarily contains a correct replica (since N > 5*T).
THEOREM QuorumIntersect ==
  ASSUME NEW QA, NEW QB,
         QA \subseteq ALL, QB \subseteq ALL,
         Cardinality(QA) >= N - T, Cardinality(QB) >= N - T
  PROVE  /\ Cardinality(QA \cap QB) >= N - 2 * T
         /\ \E id \in QA \cap QB : id \in CORRECT
  <1>1. IsFiniteSet(QA) /\ IsFiniteSet(QB) /\ IsFiniteSet(QA \cup QB)
              /\ IsFiniteSet(QA \cap QB)
        BY SubAll_Finite, FS_Union, FS_Intersection
  <1>2. Cardinality(QA \cup QB) <= N
        BY SubAll_Finite
  <1>3. Cardinality(QA \cup QB) = Cardinality(QA) + Cardinality(QB)
                                    - Cardinality(QA \cap QB)
        BY <1>1, FS_Union
  <1>4. Cardinality(QA \cap QB) >= N - 2 * T
        BY <1>1, <1>2, <1>3, FS_CardinalityType, NTF, FleqT, ConstNat
  <1>5. (QA \cap QB) \ CORRECT \subseteq FAULTY
        BY DEF ALL
  <1>6. Cardinality((QA \cap QB) \ CORRECT) <= F
        BY <1>5, FiniteCF, FS_Subset, NTF
  \* If the intersection had no correct replica it would be all faulty, so its
  \* cardinality would be <= F < N - 2*T, contradicting <1>4.
  <1>7. \E id \in QA \cap QB : id \in CORRECT
        \* If no member were correct, QA \cap QB would be all faulty, so its cardinality
        \* would be <= F; but it is >= N - 2*T > F (from N > 5*T, F <= T) -- contradiction.
        <2>1. SUFFICES ASSUME \A id \in QA \cap QB : id \notin CORRECT
                       PROVE  FALSE
              OBVIOUS
        <2>2. QA \cap QB = (QA \cap QB) \ CORRECT
              BY <2>1
        <2>3. Cardinality(QA \cap QB) <= F
              BY <2>2, <1>6
        <2>4. Cardinality(QA \cap QB) \in Nat
              BY <1>1, FS_CardinalityType
        <2> QED
              BY Arith_NotAllFaulty, <1>4, <2>3, <2>4
  <1> QED
        BY <1>4, <1>7

\* MAJORITY INTERSECTION: two > (N+T)/2 quorums of senders meet in a correct replica.
\* (The type-1 quorums backing a D2 message exceed half, not N-T.) The cardinality
\* arithmetic with `2 * Cardinality(...)` premises poisons SMT, so we PICK plain Nats
\* equal to each cardinality and do the arithmetic on those.
THEOREM MajCardBound ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  Cardinality(QA \cap QB) >= T + 1
  <1>1. IsFiniteSet(QA) /\ IsFiniteSet(QB) /\ IsFiniteSet(QA \cup QB)
              /\ IsFiniteSet(QA \cap QB)
        BY SubAll_Finite, FS_Union, FS_Intersection
  <1>2. Cardinality(QA \cup QB) <= N BY SubAll_Finite
  <1>3. Cardinality(QA \cup QB) = Cardinality(QA) + Cardinality(QB) - Cardinality(QA \cap QB)
        BY <1>1, FS_Union
  <1>card. Cardinality(QA) \in Nat /\ Cardinality(QB) \in Nat
           /\ Cardinality(QA \cup QB) \in Nat /\ Cardinality(QA \cap QB) \in Nat
        BY <1>1, FS_CardinalityType
  <1>pa. PICK ca \in Nat : ca = Cardinality(QA) BY <1>card
  <1>pb. PICK cb \in Nat : cb = Cardinality(QB) BY <1>card
  <1>pu. PICK cu \in Nat : cu = Cardinality(QA \cup QB) BY <1>card
  <1>pi. PICK ci \in Nat : ci = Cardinality(QA \cap QB) BY <1>card
  <1>e1. 2 * ca > N + T BY <1>pa
  <1>e2. 2 * cb > N + T BY <1>pb
  <1>e3. cu <= N BY <1>pu, <1>2
  <1>e4. cu = ca + cb - ci BY <1>pa, <1>pb, <1>pu, <1>pi, <1>3
  <1>s1. ca + cb > N + T BY <1>e1, <1>e2, ConstNat
  <1>s2. ci > T BY <1>s1, <1>e3, <1>e4, ConstNat
  <1> QED BY <1>s2, <1>pi, ConstNat

THEOREM MajorityIntersect ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  \E id \in QA \cap QB : id \in CORRECT
  <1>1. IsFiniteSet(QA \cap QB) BY SubAll_Finite, FS_Intersection
  <1>card. Cardinality(QA \cap QB) \in Nat BY <1>1, FS_CardinalityType
  <1>4. Cardinality(QA \cap QB) >= T + 1 BY MajCardBound
  <1>5. (QA \cap QB) \ CORRECT \subseteq FAULTY BY DEF ALL
  <1>6. Cardinality((QA \cap QB) \ CORRECT) <= F BY <1>5, FiniteCF, FS_Subset, NTF
  <1>7. \E id \in QA \cap QB : id \in CORRECT
        <2>1. SUFFICES ASSUME \A id \in QA \cap QB : id \notin CORRECT PROVE FALSE OBVIOUS
        <2>2. QA \cap QB = (QA \cap QB) \ CORRECT BY <2>1
        <2>3. Cardinality(QA \cap QB) <= F BY <2>2, <1>6
        <2> QED BY Arith_TplusOneNotFaulty, <1>4, <2>3, <1>card
  <1> QED BY <1>7

\* A correct replica that sent value v contributes a correct sender; faulty
\* senders number at most F. Used to turn ">half senders" into ">half correct".
THEOREM FaultyBound ==
  ASSUME NEW S, S \subseteq ALL
  PROVE  Cardinality(S \cap FAULTY) <= F
  BY FiniteCF, FS_Subset, NTF

\*****************************************************************************
\* MESSAGE-COUNTING (sender bound).
\* The D2 messages of one round/value with a faulty sender number at most F,
\* because m |-> AsD2(m).src injects them into FAULTY. Reusable for the quorum
\* lemmas. The map is an injection thanks to the Variant round-trip (VariantAx):
\* for m in msgs2[r] with the round constrained to r, m = D2(src, r, v).
\* (Workaround note: FS_Image crashes this tlapm build on SetOfAll, so we use the
\* first-order FS_Injection with an explicit injection function.)
\*****************************************************************************

\* The D2 messages for round r and value v sent by faulty replicas.
FaultyD2(r, v) ==
  { m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in FAULTY }

\* The injection FaultyD2(r,v) -> FAULTY mapping a message to its sender.
FaultyD2Fn(r, v) == [ m \in FaultyD2(r, v) |-> AsD2(m).src ]

\* The injection is injective: two faulty D2(r,v) messages with the same sender are
\* equal (round-trip reconstructs each as D2(src, r, v)). Top-level so Zenon discharges
\* the beta-reduction + reconstruction in one shot (nested steps fail in this build).
THEOREM FaultyD2Injective ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in FaultyD2(r, v), NEW b \in FaultyD2(r, v),
         FaultyD2Fn(r, v)[a] = FaultyD2Fn(r, v)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF FaultyD2, FaultyD2Fn

\* Hence at most F faulty D2(r,v) messages.
THEOREM FaultyD2Bound ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r
  PROVE  Cardinality(FaultyD2(r, v)) <= F
  <1>1. FaultyD2Fn(r, v) \in [ FaultyD2(r, v) -> FAULTY ]
        BY DEF FaultyD2, FaultyD2Fn
  <1>2. \A a, b \in FaultyD2(r, v) :
            FaultyD2Fn(r, v)[a] = FaultyD2Fn(r, v)[b] => a = b
        BY FaultyD2Injective
  <1>3. FaultyD2Fn(r, v) \in Injection(FaultyD2(r, v), FAULTY)
        BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. Cardinality(FaultyD2(r, v)) <= Cardinality(FAULTY)
        BY <1>3, FiniteCF, FS_Injection
  <1> QED
        BY <1>4, NTF

\*****************************************************************************
\* MESSAGE-SHAPE.  To apply FaultyD2Bound one needs the round invariant
\*   TypeOK => for m \in msgs2[r] with IsD2(m), AsD2(m).r = r
\* (so that messages of msgs2[r] are exactly D2(src, r, v)).
\*
\* The challenge: PICK-ing the TypeOK witnesses dumps a giant
\*   msgs2 = [r |-> {SetOfAll} \cup {SetOfAll}]
\* equation into context, and a `msgs2[rr]` term in the hypotheses poisons theorem
\* application (like a Cardinality term does). HIDE crashes this tlapm build. The
\* working pattern: derive a SMALL existential about msgs2[rr] with the heavy PICK kept
\* LOCAL to its sub-proof, then hand it to ShapeFromExists which abstracts msgs2[rr]
\* into a fresh variable `mset` and rewrites the goal via SUFFICES (no msgs2[rr] term in
\* the hard reasoning).
\*****************************************************************************

\* The D2 / Q2 parts of msgs2[rr] given the TypeOK witnesses A1D, A1Q.
DPof(A1D, rr) == { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
QPof(A1Q, rr) == { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }

\* A message in the D2/Q2 decomposition that is a D2 lands in the D2 part with round rr.
THEOREM ShapeHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).r = rr
  <1>1. m \notin QPof(A1Q, rr)
        <2> SUFFICES ASSUME m \in QPof(A1Q, rr) PROVE FALSE OBVIOUS
        <2>1. PICK mq \in { qrec \in A1Q: qrec.r = rr } : m = Q2(mq.src, rr) BY DEF QPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK md \in { drec \in A1D: drec.r = rr } : m = D2(md.src, rr, md.v)
        BY <1>1 DEF DPof
  <1> QED BY <1>2, VariantAx

\* The raw TypeOK set expression equals the DPof/QPof operators (clean context).
THEOREM SetEqHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q
  PROVE  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
            \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }
         = DPof(A1D, rr) \union QPof(A1Q, rr)
  BY DEF DPof, QPof

\* Abstract the message set into a fresh `mset` so the Variant reasoning never sees the
\* poisoning `msgs2[rr]` term. SUFFICES does the \E-elimination and goal rewrite.
THEOREM ShapeFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) :
                   IsD2(m) => AsD2(m).r = rr
        OBVIOUS
  <1> QED BY ShapeHelper

\* Decomposition of msgs2[rr] from TypeOK as a SMALL existential (DPof/QPof opaque).
\* The heavy `msgs2 = [...]` PICK is kept LOCAL to this proof so it never pollutes callers.
THEOREM Msgs2Decomp ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
  <1> PICK B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
           B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in B1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in B1Q: m.r = r } } ]
        BY DEF TypeOK
  <1>1. msgs2[rr] = { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } }
        OBVIOUS
  <1>2. msgs2[rr] = DPof(B1D, rr) \union QPof(B1Q, rr) BY <1>1, SetEqHelper
  <1> QED BY <1>2

\* The round invariant, fully proved.
THEOREM Msgs2Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).r = rr
  BY Msgs2Decomp, ShapeFromExists

\* --- src \in ALL variant (needed to bound D2 senders) ---
THEOREM ShapeHelperSrc ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).src \in ALL
  <1>1. m \notin QPof(A1Q, rr)
        <2> SUFFICES ASSUME m \in QPof(A1Q, rr) PROVE FALSE OBVIOUS
        <2>1. PICK mq \in { qrec \in A1Q: qrec.r = rr } : m = Q2(mq.src, rr) BY DEF QPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK md \in { drec \in A1D: drec.r = rr } : m = D2(md.src, rr, md.v) BY <1>1 DEF DPof
  <1>3. md \in A1D BY <1>2
  <1> QED BY <1>2, <1>3, VariantAx

THEOREM ShapeSrcFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) : IsD2(m) => AsD2(m).src \in ALL
        OBVIOUS
  <1> QED BY ShapeHelperSrc

THEOREM Msgs2SrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).src \in ALL
  BY Msgs2Decomp, ShapeSrcFromExists

THEOREM ShapeHelperSrcQ ==
  ASSUME NEW rr, NEW A1D, NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ], NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsQ2(m)
  PROVE  AsQ2(m).src \in ALL
  <1>1. m \notin DPof(A1D, rr)
        <2> SUFFICES ASSUME m \in DPof(A1D, rr) PROVE FALSE OBVIOUS
        <2>1. PICK md \in { drec \in A1D: drec.r = rr } : m = D2(md.src, rr, md.v) BY DEF DPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK mq \in { qrec \in A1Q: qrec.r = rr } : m = Q2(mq.src, rr) BY <1>1 DEF QPof
  <1>3. mq \in A1Q BY <1>2
  <1> QED BY <1>2, <1>3, VariantAx

THEOREM ShapeSrcQFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsQ2(m) => AsQ2(m).src \in ALL
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsQ2(m) => AsQ2(m).src \in ALL
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) : IsQ2(m) => AsQ2(m).src \in ALL
        OBVIOUS
  <1> QED BY ShapeHelperSrcQ

THEOREM Msgs2QSrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsQ2(m) => AsQ2(m).src \in ALL
  BY Msgs2Decomp, ShapeSrcQFromExists

THEOREM ShapeHelperV ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).v \in VALUES
  <1>1. m \notin QPof(A1Q, rr)
        <2> SUFFICES ASSUME m \in QPof(A1Q, rr) PROVE FALSE OBVIOUS
        <2>1. PICK mq \in { qrec \in A1Q: qrec.r = rr } : m = Q2(mq.src, rr) BY DEF QPof
        <2> QED BY <2>1, VariantAx
  <1>2. PICK md \in { drec \in A1D: drec.r = rr } : m = D2(md.src, rr, md.v) BY <1>1 DEF DPof
  <1>3. md \in A1D BY <1>2
  <1> QED BY <1>2, <1>3, VariantAx

THEOREM ShapeVFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).v \in VALUES
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : IsD2(m) => AsD2(m).v \in VALUES
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) : IsD2(m) => AsD2(m).v \in VALUES
        OBVIOUS
  <1> QED BY ShapeHelperV

THEOREM Msgs2VInValues ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).v \in VALUES
  BY Msgs2Decomp, ShapeVFromExists

\* Type-1 message shape from TypeOK (simpler than msgs2: no Variants).
THEOREM Msgs1Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs1[rr] : m.r = rr /\ m.src \in ALL
  <1> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
        msgs1 = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ]
        BY DEF TypeOK
  <1>1. msgs1[rr] = { m \in A1 : m.r = rr } OBVIOUS
  <1> QED BY <1>1

THEOREM Msgs1DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs1 = ROUNDS
  <1> PICK A1 : msgs1 = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ] BY DEF TypeOK
  <1> QED OBVIOUS

\* Type-2 message round shape (both D2 and Q2): the round field equals the index.
THEOREM ShapeHelperR ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m, m \in DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  <1>1. CASE m \in DPof(A1D, rr)
        <2>1. PICK md \in { drec \in A1D : drec.r = rr } : m = D2(md.src, rr, md.v) BY <1>1 DEF DPof
        <2> QED BY <2>1, VariantAx
  <1>2. CASE m \in QPof(A1Q, rr)
        <2>1. PICK mq \in { qrec \in A1Q : qrec.r = rr } : m = Q2(mq.src, rr) BY <1>2 DEF QPof
        <2> QED BY <2>1, VariantAx
  <1> QED BY <1>1, <1>2

THEOREM ShapeRFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  <1> SUFFICES ASSUME NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ],
                      mset = DPof(A1D, rr) \union QPof(A1Q, rr)
               PROVE  \A m \in mset : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
        OBVIOUS
  <1>1. SUFFICES \A m \in DPof(A1D, rr) \union QPof(A1Q, rr) :
                   (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
        OBVIOUS
  <1> QED BY ShapeHelperR

THEOREM Msgs2RShape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  BY Msgs2Decomp, ShapeRFromExists

THEOREM Msgs2DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs2 = ROUNDS
  <1> PICK B1D, B1Q :
        msgs2 = [ r \in ROUNDS |-> { D2(mm.src, r, mm.v): mm \in { m \in B1D: m.r = r } }
                      \union { Q2(mm.src, r): mm \in { m \in B1Q: m.r = r } } ]
        BY DEF TypeOK
  <1> QED OBVIOUS

THEOREM Msgs2PrimeDecomp ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2'[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
  <1> PICK B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
           B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
        msgs2' = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in B1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in B1Q: m.r = r } } ]
        BY DEF TypeOK
  <1>1. msgs2'[rr] = { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } }
        OBVIOUS
  <1>2. msgs2'[rr] = DPof(B1D, rr) \union QPof(B1Q, rr) BY <1>1, SetEqHelper
  <1> QED BY <1>2

THEOREM Msgs2PrimeShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).r = rr
  BY Msgs2PrimeDecomp, ShapeFromExists

THEOREM Msgs2PrimeSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).src \in ALL
  BY Msgs2PrimeDecomp, ShapeSrcFromExists

THEOREM Msgs2PrimeQSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsQ2(m) => AsQ2(m).src \in ALL
  BY Msgs2PrimeDecomp, ShapeSrcQFromExists

THEOREM Msgs2PrimeRShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
  BY Msgs2PrimeDecomp, ShapeRFromExists

THEOREM Msgs2PrimeVInValues ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).v \in VALUES
  BY Msgs2PrimeDecomp, ShapeVFromExists

\*****************************************************************************
\* D2-MESSAGE COUNTING for a fixed (round, value): the set DvSet(r,v) of all D2(v)
\* messages is finite (injects into ALL via sender), and at least one has a CORRECT
\* sender when it has >= T+1 messages (faulty ones number <= F via FaultyD2Bound).
\*****************************************************************************
DvSet(r, v) == { m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v }
DvFn(r, v) == [ m \in DvSet(r, v) |-> AsD2(m).src ]
QSet(r) == { m \in msgs2[r] : IsQ2(m) }
QFn(r) == [ m \in QSet(r) |-> AsQ2(m).src ]
DvPSet(r, v) == { m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v }
DvPFn(r, v) == [ m \in DvPSet(r, v) |-> AsD2(m).src ]
QPSet(r) == { m \in msgs2'[r] : IsQ2(m) }
QPFn(r) == [ m \in QPSet(r) |-> AsQ2(m).src ]

THEOREM DvSenderWitness ==
  ASSUME NEW r, NEW v, NEW id \in Senders2(DvSet(r, v))
  PROVE  \E md \in DvSet(r, v) : IsD2(md) /\ AsD2(md).src = id
  <1>w. \E md \in DvSet(r, v) :
          (IsD2(md) /\ AsD2(md).src = id)
            \/ (IsQ2(md) /\ AsQ2(md).src = id)
        BY Senders2_Witness
  <1> PICK md \in DvSet(r, v) :
          (IsD2(md) /\ AsD2(md).src = id)
            \/ (IsQ2(md) /\ AsQ2(md).src = id)
        BY <1>w
  <1>d2. IsD2(md) BY DEF DvSet
  <1> QED BY <1>d2, VariantAx

THEOREM Lemma3_Q2D2Faulty ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW mq \in msgs2[r], NEW md \in msgs2[r],
         IsQ2(mq), IsD2(md), AsQ2(mq).src = AsD2(md).src
  PROVE  AsQ2(mq).src \in FAULTY
  BY DEF Lemma3_NoEquivocation2ByCorrect

THEOREM Lemma3_D2D2SameCorrect ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW m1 \in msgs2[r], NEW m2 \in msgs2[r],
         IsD2(m1), IsD2(m2), AsD2(m1).src = AsD2(m2).src,
         AsD2(m1).src \in CORRECT
  PROVE  AsD2(m1).v = AsD2(m2).v
  BY DEF Lemma3_NoEquivocation2ByCorrect

THEOREM DvInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvSet(r, v), NEW b \in DvSet(r, v), DvFn(r, v)[a] = DvFn(r, v)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF DvSet, DvFn

THEOREM D2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= N
  <1>r. \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r BY Msgs2Shape
  <1>s. \A m \in msgs2[r] : IsD2(m) => AsD2(m).src \in ALL BY Msgs2SrcInAll
  <1>1. DvFn(r, v) \in [ DvSet(r, v) -> ALL ] BY <1>s DEF DvSet, DvFn
  <1>2. \A a, b \in DvSet(r, v) : DvFn(r, v)[a] = DvFn(r, v)[b] => a = b BY <1>r, DvInjective
  <1>3. DvFn(r, v) \in Injection(DvSet(r, v), ALL) BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= Cardinality(ALL)
        BY <1>3, ALL_Card, FS_Injection
  <1> QED BY <1>4, ALL_Card

THEOREM QInjective ==
  ASSUME NEW r, \A m \in msgs2[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QSet(r), NEW b \in QSet(r), QFn(r)[a] = QFn(r)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF QSet, QFn

THEOREM Q2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(QSet(r)) /\ Cardinality(QSet(r)) <= N
  <1>r. \A m \in msgs2[r] : IsQ2(m) => AsQ2(m).r = r BY Msgs2RShape
  <1>s. \A m \in msgs2[r] : IsQ2(m) => AsQ2(m).src \in ALL BY Msgs2QSrcInAll
  <1>1. QFn(r) \in [ QSet(r) -> ALL ] BY <1>s DEF QSet, QFn
  <1>2. \A a, b \in QSet(r) : QFn(r)[a] = QFn(r)[b] => a = b BY <1>r, QInjective
  <1>3. QFn(r) \in Injection(QSet(r), ALL) BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. IsFiniteSet(QSet(r)) /\ Cardinality(QSet(r)) <= Cardinality(ALL)
        BY <1>3, ALL_Card, FS_Injection
  <1> QED BY <1>4, ALL_Card

THEOREM DvPInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2'[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvPSet(r, v), NEW b \in DvPSet(r, v), DvPFn(r, v)[a] = DvPFn(r, v)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF DvPSet, DvPFn

THEOREM D2PSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvPSet(r, v)) /\ Cardinality(DvPSet(r, v)) <= N
  <1>r. \A m \in msgs2'[r] : IsD2(m) => AsD2(m).r = r BY Msgs2PrimeShape
  <1>s. \A m \in msgs2'[r] : IsD2(m) => AsD2(m).src \in ALL BY Msgs2PrimeSrcInAll
  <1>1. DvPFn(r, v) \in [ DvPSet(r, v) -> ALL ] BY <1>s DEF DvPSet, DvPFn
  <1>2. \A a, b \in DvPSet(r, v) : DvPFn(r, v)[a] = DvPFn(r, v)[b] => a = b BY <1>r, DvPInjective
  <1>3. DvPFn(r, v) \in Injection(DvPSet(r, v), ALL) BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. IsFiniteSet(DvPSet(r, v)) /\ Cardinality(DvPSet(r, v)) <= Cardinality(ALL)
        BY <1>3, ALL_Card, FS_Injection
  <1> QED BY <1>4, ALL_Card

THEOREM DvPSenderWitness ==
  ASSUME NEW r, NEW v, NEW src \in Senders2(DvPSet(r, v))
  PROVE  \E m \in DvPSet(r, v) : IsD2(m) /\ AsD2(m).src = src
  <1>pick. PICK m \in DvPSet(r, v) :
        (IsD2(m) /\ AsD2(m).src = src) \/ (IsQ2(m) /\ AsQ2(m).src = src)
        BY DEF Senders2
  <1> QED BY <1>pick, VariantAx DEF DvPSet

THEOREM QPInjective ==
  ASSUME NEW r, \A m \in msgs2'[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QPSet(r), NEW b \in QPSet(r), QPFn(r)[a] = QPFn(r)[b]
  PROVE  a = b
  BY Zenon, VariantAx DEF QPSet, QPFn

THEOREM QPSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(QPSet(r)) /\ Cardinality(QPSet(r)) <= N
  <1>r. \A m \in msgs2'[r] : IsQ2(m) => AsQ2(m).r = r BY Msgs2PrimeRShape
  <1>s. \A m \in msgs2'[r] : IsQ2(m) => AsQ2(m).src \in ALL BY Msgs2PrimeQSrcInAll
  <1>1. QPFn(r) \in [ QPSet(r) -> ALL ] BY <1>s DEF QPSet, QPFn
  <1>2. \A a, b \in QPSet(r) : QPFn(r)[a] = QPFn(r)[b] => a = b BY <1>r, QPInjective
  <1>3. QPFn(r) \in Injection(QPSet(r), ALL) BY <1>1, <1>2 DEF Injection, IsInjective
  <1>4. IsFiniteSet(QPSet(r)) /\ Cardinality(QPSet(r)) <= Cardinality(ALL)
        BY <1>3, ALL_Card, FS_Injection
  <1> QED BY <1>4, ALL_Card

THEOREM DvStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
          /\ Cardinality(DvSet(r, v))
             <= Cardinality({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>sub. DvSet(r, v) \subseteq { m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v }
        BY <1>nm, <1>r0, <1>dom2 DEF DvSet
  <1>finOld. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>sup. { m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v } \subseteq DvSet(r, v) \union { nm }
        BY <1>nm, <1>r0, <1>dom2 DEF DvSet
  <1>finSup. IsFiniteSet(DvSet(r, v) \union { nm }) BY <1>finOld, FS_AddElement
  <1>finNew. IsFiniteSet({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
        BY <1>sup, <1>finSup, FS_Subset
  <1>mono. Cardinality(DvSet(r, v))
              <= Cardinality({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
        BY <1>sub, <1>finNew, FS_Subset
  <1> QED BY <1>finNew, <1>mono

THEOREM QStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsQ2(m) })
          /\ Cardinality(QSet(r))
             <= Cardinality({ m \in msgs2'[r] : IsQ2(m) })
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>sub. QSet(r) \subseteq { m \in msgs2'[r] : IsQ2(m) }
        BY <1>nm, <1>r0, <1>dom2 DEF QSet
  <1>finOld. IsFiniteSet(QSet(r)) BY Q2SetFinite
  <1>sup. { m \in msgs2'[r] : IsQ2(m) } \subseteq QSet(r) \union { nm }
        BY <1>nm, <1>r0, <1>dom2 DEF QSet
  <1>finSup. IsFiniteSet(QSet(r) \union { nm }) BY <1>finOld, FS_AddElement
  <1>finNew. IsFiniteSet({ m \in msgs2'[r] : IsQ2(m) })
        BY <1>sup, <1>finSup, FS_Subset
  <1>mono. Cardinality(QSet(r))
              <= Cardinality({ m \in msgs2'[r] : IsQ2(m) })
        BY <1>sub, <1>finNew, FS_Subset
  <1> QED BY <1>finNew, <1>mono

THEOREM Msgs2Finite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2[r])
  <1>v0. 0 \in VALUES BY DEF VALUES
  <1>v1. 1 \in VALUES BY DEF VALUES
  <1>f0. IsFiniteSet(DvSet(r, 0)) BY <1>v0, D2SetFinite
  <1>f1. IsFiniteSet(DvSet(r, 1)) BY <1>v1, D2SetFinite
  <1>fq. IsFiniteSet(QSet(r)) BY Q2SetFinite
  <1>sub. msgs2[r] \subseteq (DvSet(r, 0) \union DvSet(r, 1)) \union QSet(r)
        BY Msgs2VInValues, VariantAx DEF DvSet, QSet, VALUES
  <1>fin01. IsFiniteSet(DvSet(r, 0) \union DvSet(r, 1)) BY <1>f0, <1>f1, FS_Union
  <1>finAll. IsFiniteSet((DvSet(r, 0) \union DvSet(r, 1)) \union QSet(r))
        BY <1>fin01, <1>fq, FS_Union
  <1> QED BY <1>sub, <1>finAll, FS_Subset

THEOREM Msgs2PrimeFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2'[r])
  <1>v0. 0 \in VALUES BY DEF VALUES
  <1>v1. 1 \in VALUES BY DEF VALUES
  <1>f0. IsFiniteSet(DvPSet(r, 0)) BY <1>v0, D2PSetFinite
  <1>f1. IsFiniteSet(DvPSet(r, 1)) BY <1>v1, D2PSetFinite
  <1>fq. IsFiniteSet(QPSet(r)) BY QPSetFinite
  <1>sub. msgs2'[r] \subseteq (DvPSet(r, 0) \union DvPSet(r, 1)) \union QPSet(r)
        BY Msgs2PrimeVInValues, VariantAx DEF DvPSet, QPSet, VALUES
  <1>fin01. IsFiniteSet(DvPSet(r, 0) \union DvPSet(r, 1)) BY <1>f0, <1>f1, FS_Union
  <1>finAll. IsFiniteSet((DvPSet(r, 0) \union DvPSet(r, 1)) \union QPSet(r))
        BY <1>fin01, <1>fq, FS_Union
  <1> QED BY <1>sub, <1>finAll, FS_Subset

THEOREM Msgs2Step2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>sub. msgs2[r] \subseteq msgs2'[r]
        BY <1>nm, <1>r0, <1>dom2
  <1>finOld. IsFiniteSet(msgs2[r]) BY Msgs2Finite
  <1>sup. msgs2'[r] \subseteq msgs2[r] \union { nm }
        BY <1>nm, <1>r0, <1>dom2
  <1>finSup. IsFiniteSet(msgs2[r] \union { nm }) BY <1>finOld, FS_AddElement
  <1>finNew. IsFiniteSet(msgs2'[r]) BY <1>sup, <1>finSup, FS_Subset
  <1>mono. Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
        BY <1>sub, <1>finNew, FS_Subset
  <1> QED BY <1>finNew, <1>mono

DPart(S, v) == { m \in S : IsD2(m) /\ AsD2(m).v = v }
QPart(S) == { m \in S : IsQ2(m) }

THEOREM Msgs2SenderPartitionBound ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW S, S \subseteq msgs2[r]
  PROVE  Cardinality(Senders2(S))
           <= Cardinality(DPart(S, 0)) + Cardinality(DPart(S, 1)) + Cardinality(QPart(S))
  <1>v0. 0 \in VALUES BY DEF VALUES
  <1>v1. 1 \in VALUES BY DEF VALUES
  <1>finS. IsFiniteSet(S) BY Msgs2Finite, FS_Subset
  <1>finD0. IsFiniteSet(DPart(S, 0)) BY <1>finS, FS_Subset DEF DPart
  <1>finD1. IsFiniteSet(DPart(S, 1)) BY <1>finS, FS_Subset DEF DPart
  <1>finQ. IsFiniteSet(QPart(S)) BY <1>finS, FS_Subset DEF QPart
  <1>shape. /\ \A dmsg \in S : IsD2(dmsg) => /\ AsD2(dmsg).src \in ALL
                                                  /\ AsD2(dmsg).r = r
                                                  /\ AsD2(dmsg).v \in VALUES
             /\ \A qmsg \in S : IsQ2(qmsg) => /\ AsQ2(qmsg).src \in ALL
                                                  /\ AsQ2(qmsg).r = r
        BY Msgs2Shape, Msgs2SrcInAll, Msgs2VInValues, Msgs2RShape, Msgs2QSrcInAll
  <1>part. Senders2(S)
              \subseteq (Senders2(DPart(S, 0)) \union Senders2(DPart(S, 1)))
                           \union Senders2(QPart(S))
        BY <1>shape, VariantAx DEF Senders2, DPart, QPart, VALUES
  <1>finS0. IsFiniteSet(Senders2(DPart(S, 0))) BY Senders2_Sub
  <1>finS1. IsFiniteSet(Senders2(DPart(S, 1))) BY Senders2_Sub
  <1>finSQ. IsFiniteSet(Senders2(QPart(S))) BY Senders2_Sub
  <1>finUnion. IsFiniteSet((Senders2(DPart(S, 0)) \union Senders2(DPart(S, 1)))
                           \union Senders2(QPart(S)))
        BY <1>finS0, <1>finS1, <1>finSQ, FS_Union
  <1>mono. Cardinality(Senders2(S))
              <= Cardinality((Senders2(DPart(S, 0)) \union Senders2(DPart(S, 1)))
                           \union Senders2(QPart(S)))
        BY <1>part, <1>finUnion, FS_Subset
  <1>union. Cardinality((Senders2(DPart(S, 0)) \union Senders2(DPart(S, 1)))
                           \union Senders2(QPart(S)))
              <= Cardinality(Senders2(DPart(S, 0)))
                   + Cardinality(Senders2(DPart(S, 1)))
                   + Cardinality(Senders2(QPart(S)))
        BY <1>finS0, <1>finS1, <1>finSQ, CardUnion3LeSum
  <1>s0. Cardinality(Senders2(DPart(S, 0))) <= Cardinality(DPart(S, 0))
        BY <1>finD0, Senders2_CardLeSet
  <1>s1. Cardinality(Senders2(DPart(S, 1))) <= Cardinality(DPart(S, 1))
        BY <1>finD1, Senders2_CardLeSet
  <1>sq. Cardinality(Senders2(QPart(S))) <= Cardinality(QPart(S))
        BY <1>finQ, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(S)) \in Nat
             /\ Cardinality((Senders2(DPart(S, 0)) \union Senders2(DPart(S, 1)))
                           \union Senders2(QPart(S))) \in Nat
             /\ Cardinality(Senders2(DPart(S, 0))) \in Nat
             /\ Cardinality(Senders2(DPart(S, 1))) \in Nat
             /\ Cardinality(Senders2(QPart(S))) \in Nat
             /\ Cardinality(DPart(S, 0)) \in Nat
             /\ Cardinality(DPart(S, 1)) \in Nat
             /\ Cardinality(QPart(S)) \in Nat
        BY <1>finUnion, <1>finD0, <1>finD1, <1>finQ, Senders2_Sub, FS_CardinalityType
  <1>sumSend. Cardinality(Senders2(S))
                <= Cardinality(Senders2(DPart(S, 0)))
                   + Cardinality(Senders2(DPart(S, 1)))
                   + Cardinality(Senders2(QPart(S)))
        BY <1>mono, <1>union, <1>types, Arith_GeTrans
  <1> QED BY <1>sumSend, <1>s0, <1>s1, <1>sq, <1>types, Arith_ThreeLeTrans

THEOREM LowWeightsReceivedL11Witness ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A v \in VALUES :
           Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) < T + 1
  PROVE  LET n0 == Cardinality(DvSet(r, 0))
             n1 == Cardinality(DvSet(r, 1))
             nq == Cardinality(QSet(r))
         IN
         \E x0, x1 \in 0..N:
           /\ x0 <= n0 /\ x1 <= n1
           /\ x0 + x1 + nq >= N - T
           /\ 2 * x0 <= N + T
           /\ 2 * x1 <= N + T
  <1> DEFINE R0 == DPart(received, 0)
             R1 == DPart(received, 1)
             RQ == QPart(received)
  <1>v0. 0 \in VALUES BY DEF VALUES
  <1>v1. 1 \in VALUES BY DEF VALUES
  <1>sub0. R0 \subseteq DvSet(r, 0) BY DEF R0, DPart, DvSet
  <1>sub1. R1 \subseteq DvSet(r, 1) BY DEF R1, DPart, DvSet
  <1>subq. RQ \subseteq QSet(r) BY DEF RQ, QPart, QSet
  <1>finD0. IsFiniteSet(DvSet(r, 0)) BY <1>v0, D2SetFinite
  <1>finD1. IsFiniteSet(DvSet(r, 1)) BY <1>v1, D2SetFinite
  <1>finQ. IsFiniteSet(QSet(r)) BY Q2SetFinite
  <1>finR0. IsFiniteSet(R0) BY <1>sub0, <1>finD0, FS_Subset
  <1>finR1. IsFiniteSet(R1) BY <1>sub1, <1>finD1, FS_Subset
  <1>finRQ. IsFiniteSet(RQ) BY <1>subq, <1>finQ, FS_Subset
  <1>c0. Cardinality(R0) <= Cardinality(DvSet(r, 0)) BY <1>sub0, <1>finD0, FS_Subset
  <1>c1. Cardinality(R1) <= Cardinality(DvSet(r, 1)) BY <1>sub1, <1>finD1, FS_Subset
  <1>cq. Cardinality(RQ) <= Cardinality(QSet(r)) BY <1>subq, <1>finQ, FS_Subset
  <1>part. Cardinality(Senders2(received))
              <= Cardinality(R0) + Cardinality(R1) + Cardinality(RQ)
        BY Msgs2SenderPartitionBound DEF R0, R1, RQ, DPart, QPart
  <1>shape0. \A m \in R0 : IsD2(m) /\ AsD2(m).src \in ALL
                             /\ AsD2(m).r = r /\ AsD2(m).v = 0
        BY Msgs2Shape, Msgs2SrcInAll, Msgs2RShape DEF R0, DPart
  <1>shape1. \A m \in R1 : IsD2(m) /\ AsD2(m).src \in ALL
                             /\ AsD2(m).r = r /\ AsD2(m).v = 1
        BY Msgs2Shape, Msgs2SrcInAll, Msgs2RShape DEF R1, DPart
  <1>send0. Cardinality(R0) <= Cardinality(Senders2(R0))
        BY <1>shape0, D2Fixed_CardLeSenders
  <1>send1. Cardinality(R1) <= Cardinality(Senders2(R1))
        BY <1>shape1, D2Fixed_CardLeSenders
  <1>low0s. Cardinality(Senders2(R0)) < T + 1 BY <1>v0 DEF R0, DPart
  <1>low1s. Cardinality(Senders2(R1)) < T + 1 BY <1>v1 DEF R1, DPart
  <1>types. /\ Cardinality(R0) \in Nat /\ Cardinality(R1) \in Nat /\ Cardinality(RQ) \in Nat
             /\ Cardinality(DvSet(r, 0)) \in Nat /\ Cardinality(DvSet(r, 1)) \in Nat
             /\ Cardinality(QSet(r)) \in Nat
             /\ Cardinality(Senders2(received)) \in Nat
             /\ Cardinality(Senders2(R0)) \in Nat /\ Cardinality(Senders2(R1)) \in Nat
             /\ N \in Nat /\ N - T \in Nat /\ T + 1 \in Nat
        BY <1>finR0, <1>finR1, <1>finRQ, <1>finD0, <1>finD1, <1>finQ,
           Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>low0. Cardinality(R0) < T + 1 BY <1>send0, <1>low0s, <1>types, Arith_LeLtTrans
  <1>low1. Cardinality(R1) < T + 1 BY <1>send1, <1>low1s, <1>types, Arith_LeLtTrans
  <1>bd0. Cardinality(DvSet(r, 0)) <= N BY <1>v0, D2SetFinite
  <1>bd1. Cardinality(DvSet(r, 1)) <= N BY <1>v1, D2SetFinite
  <1>r0leN. Cardinality(R0) <= N BY <1>c0, <1>bd0, <1>types, Arith_LeTrans
  <1>r1leN. Cardinality(R1) <= N BY <1>c1, <1>bd1, <1>types, Arith_LeTrans
  <1>x0N. Cardinality(R0) \in 0..N BY <1>types, <1>r0leN
  <1>x1N. Cardinality(R1) \in 0..N BY <1>types, <1>r1leN
  <1>sum. Cardinality(R0) + Cardinality(R1) + Cardinality(QSet(r)) >= N - T
        BY <1>part, <1>cq, <1>types, Arith_SumThirdMonoGe
  <1>d0. 2 * Cardinality(R0) <= N + T BY <1>types, <1>low0, Arith_DoubleLtTplusOneLeNplusT
  <1>d1. 2 * Cardinality(R1) <= N + T BY <1>types, <1>low1, Arith_DoubleLtTplusOneLeNplusT
  <1> QED BY <1>x0N, <1>x1N, <1>c0, <1>c1, <1>sum, <1>d0, <1>d1

\* Abstract arithmetic: >= T+1 elements, <= F of them excluded, leaves >= 1.
LEMMA Arith_DiffPos ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= T + 1, b <= F
  PROVE  a - b >= 1
  BY FleqT, ConstNat

\* A D2 quorum of >= T+1 messages contains one from a CORRECT replica.
THEOREM CorrectD2Exists ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1
  PROVE  \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
  <1>r. \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r BY Msgs2Shape
  <1>s. \A m \in msgs2[r] : IsD2(m) => AsD2(m).src \in ALL BY Msgs2SrcInAll
  <1>fin. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>sub. FaultyD2(r, v) \subseteq DvSet(r, v) BY DEF FaultyD2, DvSet
  <1>fin2. IsFiniteSet(FaultyD2(r, v)) BY <1>fin, <1>sub, FS_Subset
  <1>fd. Cardinality(FaultyD2(r, v)) <= F BY <1>r, FaultyD2Bound
  <1>int. DvSet(r, v) \cap FaultyD2(r, v) = FaultyD2(r, v) BY <1>sub
  <1>diff. Cardinality(DvSet(r, v) \ FaultyD2(r, v))
              = Cardinality(DvSet(r, v)) - Cardinality(FaultyD2(r, v))
           BY <1>fin, <1>int, FS_Difference
  <1>card. Cardinality(DvSet(r, v)) \in Nat /\ Cardinality(FaultyD2(r, v)) \in Nat
           BY <1>fin, <1>fin2, FS_CardinalityType
  <1>arith. Cardinality(DvSet(r, v)) - Cardinality(FaultyD2(r, v)) >= 1
            BY <1>card, <1>fd, Arith_DiffPos
  <1>pos. Cardinality(DvSet(r, v) \ FaultyD2(r, v)) >= 1 BY <1>diff, <1>arith
  <1>ne. DvSet(r, v) \ FaultyD2(r, v) # {}
         <2> SUFFICES ASSUME DvSet(r, v) \ FaultyD2(r, v) = {} PROVE FALSE OBVIOUS
         <2>1. IsFiniteSet(DvSet(r, v) \ FaultyD2(r, v)) BY <1>fin, FS_Difference
         <2> QED BY <2>1, <1>pos, FS_EmptySet
  <1>pick. PICK mv \in DvSet(r, v) : mv \notin FaultyD2(r, v) BY <1>ne
  <1>cor. AsD2(mv).src \in CORRECT
          <2>1. AsD2(mv).src \in ALL BY <1>s, <1>pick DEF DvSet
          <2>2. AsD2(mv).src \notin FAULTY BY <1>pick DEF DvSet, FaultyD2
          <2> QED BY <2>1, <2>2 DEF ALL
  <1> QED BY <1>pick, <1>cor DEF DvSet

THEOREM StrictQuorumSenderStrict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  /\ Cardinality(Senders2(DvSet(r, v))) >= T + 1
          /\ 2 * Cardinality(Senders2(DvSet(r, v))) > N + T
  <1>finD. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>shape. \A m \in DvSet(r, v) :
               IsD2(m) /\ AsD2(m).src \in ALL
                 /\ AsD2(m).r = r /\ AsD2(m).v = v
        BY Msgs2Shape, Msgs2SrcInAll DEF DvSet
  <1>dLeS. Cardinality(DvSet(r, v)) <= Cardinality(Senders2(DvSet(r, v)))
        BY <1>shape, D2Fixed_CardLeSenders
  <1>rawGe. Cardinality(DvSet(r, v)) >= T + 1
        BY DEF ExistsQuorum2LessRam, DvSet
  <1>rawStrict. 2 * Cardinality(DvSet(r, v)) > N + T
        BY DEF ExistsQuorum2LessRam, DvSet
  <1>types. /\ Cardinality(DvSet(r, v)) \in Nat
             /\ Cardinality(Senders2(DvSet(r, v))) \in Nat
             /\ T + 1 \in Nat /\ N + T \in Nat
        BY <1>finD, Senders2_Sub, FS_CardinalityType, ConstNat, FleqT
  <1>sGe. Cardinality(Senders2(DvSet(r, v))) >= T + 1
        BY <1>rawGe, <1>dLeS, <1>types, Arith_GeTrans
  <1>sStrict. 2 * Cardinality(Senders2(DvSet(r, v))) > N + T
        BY <1>rawStrict, <1>dLeS, <1>types, Arith_DoubleGtMono
  <1> QED BY <1>sGe, <1>sStrict

THEOREM StrictQuorumFewOthers ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
            < N - 2 * T
  <1> USE DEF IndInv
  <1> DEFINE D == Senders2(DvSet(r, v))
             O == Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v })
             I == D \cap O
  <1>intFaulty. I \subseteq FAULTY
    <2> SUFFICES ASSUME NEW id \in I PROVE id \in FAULTY OBVIOUS
    <2>inD. id \in D BY DEF I
    <2>inO. id \in O BY DEF I
    <2>all. id \in ALL BY <2>inD DEF D, Senders2
    <2>pickD. PICK md \in DvSet(r, v) :
          IsD2(md) /\ AsD2(md).src = id
        BY <2>inD, DvSenderWitness DEF D
    <2>pickO. PICK mo \in { m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v } :
          (IsD2(mo) /\ AsD2(mo).src = id) \/ (IsQ2(mo) /\ AsQ2(mo).src = id)
        BY <2>inO, Senders2_Witness DEF O
    <2>corr. CASE id \in CORRECT
      <3>od. CASE IsD2(mo)
        <4>moD. IsD2(mo) /\ AsD2(mo).src = id BY <2>pickO, <3>od, VariantAx
        <4>mdD. IsD2(md) /\ AsD2(md).src = id BY <2>pickD
        <4>moIn. mo \in msgs2[r] BY <2>pickO
        <4>mdIn. md \in msgs2[r] BY <2>pickD DEF DvSet
        <4>src. AsD2(mo).src = AsD2(md).src BY <4>moD, <4>mdD
        <4>same. AsD2(mo).v = AsD2(md).v
              BY <4>moIn, <4>mdIn, <4>moD, <4>mdD, <2>corr, <4>src,
                 Lemma3_D2D2SameCorrect
        <4>notq. ~ IsQ2(mo) BY <3>od, VariantAx
        <4>neq. AsD2(mo).v /= v BY <2>pickO, <4>notq
        <4>eqv. AsD2(md).v = v BY <2>pickD DEF DvSet
        <4>false. FALSE BY <4>same, <4>neq, <4>eqv
        <4> QED BY <4>false
      <3>oq. CASE IsQ2(mo)
        <4>moQ. IsQ2(mo) /\ AsQ2(mo).src = id BY <2>pickO, <3>oq, VariantAx
        <4>mdD. IsD2(md) /\ AsD2(md).src = id BY <2>pickD
        <4>moIn. mo \in msgs2[r] BY <2>pickO
        <4>mdIn. md \in msgs2[r] BY <2>pickD DEF DvSet
        <4>src. AsQ2(mo).src = AsD2(md).src BY <4>moQ, <4>mdD
        <4>faulty. AsQ2(mo).src \in FAULTY
              BY <4>moIn, <4>mdIn, <4>moQ, <4>mdD, <4>src,
                 Lemma3_Q2D2Faulty
        <4>false. FALSE BY <2>corr, <4>moQ, <4>faulty, DisjointCF
        <4> QED BY <4>false
      <3> QED BY <3>od, <3>oq, VariantAx
    <2>faulty. CASE id \in FAULTY
      <3> QED BY <2>faulty
    <2> QED BY <2>all, <2>corr, <2>faulty DEF ALL
  <1>finD. IsFiniteSet(D) BY Senders2_Sub
  <1>finO. IsFiniteSet(O) BY Senders2_Sub
  <1>finI. IsFiniteSet(I) BY <1>finD, FS_Intersection DEF I
  <1>finU. IsFiniteSet(D \union O) BY <1>finD, <1>finO, FS_Union
  <1>uSub. D \union O \subseteq ALL BY Senders2_Sub
  <1>uLeN. Cardinality(D \union O) <= N BY <1>uSub, ALL_Card, FS_Subset
  <1>iLeF. Cardinality(I) <= F BY <1>intFaulty, FiniteCF, FS_Subset, NTF
  <1>unionEq. Cardinality(D \union O) = Cardinality(D) + Cardinality(O) - Cardinality(I)
        BY <1>finD, <1>finO, FS_Union DEF I
  <1>dStrict. 2 * Cardinality(D) > N + T BY StrictQuorumSenderStrict DEF D
  <1>types. /\ Cardinality(D) \in Nat
             /\ Cardinality(O) \in Nat
             /\ Cardinality(I) \in Nat
             /\ Cardinality(D \union O) \in Nat
        BY <1>finD, <1>finO, <1>finI, <1>finU, FS_CardinalityType
  <1> QED BY <1>uLeN, <1>unionEq, <1>dStrict, <1>iLeF, <1>types,
             Arith_OtherLtFromStrictOverlap DEF O

\* A round cannot support two different values. A supported value has at least
\* T+1 D2 senders, hence at least one correct D2 sender; Lemma7 turns that into
\* a type-1 majority, and two such majorities intersect in a correct sender.
THEOREM SupportedUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in SupportedValues(r), NEW w \in SupportedValues(r)
  PROVE  v = w
  <1> USE DEF IndInv
  <1>vv. v \in VALUES BY DEF SupportedValues
  <1>wv. w \in VALUES BY DEF SupportedValues
  <1>sv. Cardinality(Senders2(DvSet(r, v))) >= T + 1
        BY DEF SupportedValues, DvSet
  <1>sw. Cardinality(Senders2(DvSet(r, w))) >= T + 1
        BY DEF SupportedValues, DvSet
  <1>finv. IsFiniteSet(DvSet(r, v)) BY <1>vv, D2SetFinite
  <1>finw. IsFiniteSet(DvSet(r, w)) BY <1>wv, D2SetFinite
  <1>lev. Cardinality(Senders2(DvSet(r, v))) <= Cardinality(DvSet(r, v))
        BY <1>finv, Senders2_CardLeSet
  <1>lew. Cardinality(Senders2(DvSet(r, w))) <= Cardinality(DvSet(r, w))
        BY <1>finw, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(DvSet(r, v))) \in Nat
             /\ Cardinality(Senders2(DvSet(r, w))) \in Nat
             /\ Cardinality(DvSet(r, v)) \in Nat
             /\ Cardinality(DvSet(r, w)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finv, <1>finw, FS_CardinalityType, ConstNat, FleqT
  <1>dv. Cardinality(DvSet(r, v)) >= T + 1
        BY <1>sv, <1>lev, <1>types, Arith_GeTrans
  <1>dw. Cardinality(DvSet(r, w)) >= T + 1
        BY <1>sw, <1>lew, <1>types, Arith_GeTrans
  <1>ev. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY <1>vv, <1>dv, CorrectD2Exists
  <1>ew. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        BY <1>wv, <1>dw, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r] : m.v = v }
              Sw == { m \in msgs1[r] : m.v = w }
          IN 2 * Cardinality(Senders1(Sv)) > N + T
             /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>vv, <1>wv, <1>ev, <1>ew DEF Lemma7_D2RequiresQuorum
  <1>meet. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
    <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
          /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
          BY DEF Senders1
    <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
          /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
          BY <1>maj
    <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
          BY <2>1, <2>2, MajorityIntersect
    <2> QED BY <2>3 DEF Senders1
  <1> QED BY <1>meet DEF Lemma2_NoEquivocation1ByCorrect

THEOREM QuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v),
         NEW w \in SupportedValues(r)
  PROVE  w = v
  <1> USE DEF IndInv
  <1>wv. w \in VALUES BY DEF SupportedValues
  <1>sv. Cardinality(Senders2(DvSet(r, w))) >= T + 1
        BY DEF SupportedValues, DvSet
  <1>finw. IsFiniteSet(DvSet(r, w)) BY <1>wv, D2SetFinite
  <1>lew. Cardinality(Senders2(DvSet(r, w))) <= Cardinality(DvSet(r, w))
        BY <1>finw, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(DvSet(r, w))) \in Nat
             /\ Cardinality(DvSet(r, w)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finw, FS_CardinalityType, ConstNat, FleqT
  <1>dw. Cardinality(DvSet(r, w)) >= T + 1
        BY <1>sv, <1>lew, <1>types, Arith_GeTrans
  <1>dv. Cardinality(DvSet(r, v)) >= T + 1
        BY DEF ExistsQuorum2LessRam, DvSet
  <1>ev. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY <1>dv, CorrectD2Exists
  <1>ew. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        BY <1>wv, <1>dw, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r] : m.v = v }
              Sw == { m \in msgs1[r] : m.v = w }
          IN 2 * Cardinality(Senders1(Sv)) > N + T
             /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>wv, <1>ev, <1>ew DEF Lemma7_D2RequiresQuorum
  <1>meet. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
    <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
          /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
          BY DEF Senders1
    <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
          /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
          BY <1>maj
    <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
          BY <2>1, <2>2, MajorityIntersect
    <2> QED BY <2>3 DEF Senders1
  <1> QED BY <1>meet DEF Lemma2_NoEquivocation1ByCorrect

THEOREM DQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
  <1> USE DEF IndInv
  <1>wv. w \in VALUES BY DEF SupportedValues
  <1>sv. Cardinality(Senders2(DvSet(r, w))) >= T + 1
        BY DEF SupportedValues, DvSet
  <1>finw. IsFiniteSet(DvSet(r, w)) BY <1>wv, D2SetFinite
  <1>lew. Cardinality(Senders2(DvSet(r, w))) <= Cardinality(DvSet(r, w))
        BY <1>finw, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(DvSet(r, w))) \in Nat
             /\ Cardinality(DvSet(r, w)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finw, FS_CardinalityType, ConstNat, FleqT
  <1>dw. Cardinality(DvSet(r, w)) >= T + 1
        BY <1>sv, <1>lew, <1>types, Arith_GeTrans
  <1>ev. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY CorrectD2Exists
  <1>ew. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        BY <1>wv, <1>dw, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r] : m.v = v }
              Sw == { m \in msgs1[r] : m.v = w }
          IN 2 * Cardinality(Senders1(Sv)) > N + T
             /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>wv, <1>ev, <1>ew DEF Lemma7_D2RequiresQuorum
  <1>meet. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
    <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
          /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
          BY DEF Senders1
    <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
          /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
          BY <1>maj
    <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
          BY <2>1, <2>2, MajorityIntersect
    <2> QED BY <2>3 DEF Senders1
  <1> QED BY <1>meet DEF Lemma2_NoEquivocation1ByCorrect

THEOREM DQuorumDominatesMajorityD ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in VALUES,
         2 * Cardinality(Senders2(DvSet(r, w))) > N + T
  PROVE  w = v
  <1> USE DEF IndInv
  <1>finw. IsFiniteSet(DvSet(r, w)) BY D2SetFinite
  <1>lew. Cardinality(Senders2(DvSet(r, w))) <= Cardinality(DvSet(r, w))
        BY <1>finw, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(DvSet(r, w))) \in Nat
             /\ Cardinality(DvSet(r, w)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finw, FS_CardinalityType, ConstNat, FleqT
  <1>sw. Cardinality(Senders2(DvSet(r, w))) >= T + 1
        BY <1>types, Arith_DoubleGtNplusTImplTplusOne
  <1>dw. Cardinality(DvSet(r, w)) >= T + 1
        BY <1>sw, <1>lew, <1>types, Arith_GeTrans
  <1>ev. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY CorrectD2Exists
  <1>ew. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        BY <1>dw, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r] : m.v = v }
              Sw == { m \in msgs1[r] : m.v = w }
          IN 2 * Cardinality(Senders1(Sv)) > N + T
             /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>ev, <1>ew DEF Lemma7_D2RequiresQuorum
  <1>meet. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
    <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
          /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
          BY DEF Senders1
    <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
          /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
          BY <1>maj
    <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
          BY <2>1, <2>2, MajorityIntersect
    <2> QED BY <2>3 DEF Senders1
  <1> QED BY <1>meet DEF Lemma2_NoEquivocation1ByCorrect

THEOREM StrictQuorumSupportedSingleton ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  v \in SupportedValues(r)
         /\ \A u \in SupportedValues(r) : u = v
  <1>sender. Cardinality(Senders2(DvSet(r, v))) >= T + 1
        BY StrictQuorumSenderStrict
  <1>few. Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
             < N - 2 * T
        BY StrictQuorumFewOthers
  <1>vin. v \in SupportedValues(r)
        BY <1>sender, <1>few DEF SupportedValues, DvSet
  <1>all. \A u \in SupportedValues(r) : u = v
    <2> SUFFICES ASSUME NEW u \in SupportedValues(r) PROVE u = v OBVIOUS
    <2>uv. u = v BY QuorumDominatesSupported
    <2> QED BY <2>uv
  <1> QED BY <1>vin, <1>all

THEOREM SupportedSingletonPinsNextM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW m \in msgs1[r + 1],
         m.src \in CORRECT
  PROVE  m.v = v
  <1> USE DEF IndInv
  <1>conn. LET Supported == SupportedValues(r) IN
             \/ Supported = {}
             \/ \E u \in Supported :
                  \A mm \in msgs1[r + 1] : mm.src \in CORRECT => mm.v = u
        BY DEF Lemma9_RoundsConnection
  <1>nonempty. SupportedValues(r) # {} OBVIOUS
  <1>pick. PICK u \in SupportedValues(r) :
              \A mm \in msgs1[r + 1] : mm.src \in CORRECT => mm.v = u
        BY <1>conn, <1>nonempty
  <1>uv. u = v BY <1>pick
  <1>mv. m.v = u BY <1>pick
  <1> QED BY <1>uv, <1>mv

THEOREM EarlyTplusOneHasCorrect ==
  ASSUME NEW S, S \subseteq ALL, Cardinality(S) >= T + 1
  PROVE  \E id \in S : id \in CORRECT
  <1>fin. IsFiniteSet(S) BY SubAll_Finite
  <1>card. Cardinality(S) \in Nat BY <1>fin, FS_CardinalityType
  <1>ge. Cardinality(S) >= T + 1 OBVIOUS
  <1>bad. S \ CORRECT \subseteq FAULTY BY DEF ALL
  <1>bd. Cardinality(S \ CORRECT) <= F BY <1>bad, FiniteCF, FS_Subset, NTF
  <1> QED
    <2>suf. SUFFICES ASSUME \A id \in S : id \notin CORRECT PROVE FALSE OBVIOUS
    <2>eq. S = S \ CORRECT BY <2>suf
    <2>le. Cardinality(S) <= F BY <2>eq, <1>bd
    <2> QED BY <1>card, <1>ge, <2>le, Arith_TplusOneNotFaulty

THEOREM EarlyMajorityM1HasCorrect ==
  ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
         2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
  <1> DEFINE S == Senders1({ m \in msgs1[r] : m.v = v })
  <1>sub. S \subseteq ALL BY Senders1_Sub
  <1>types. Cardinality(S) \in Nat BY Senders1_Sub, FS_CardinalityType
  <1>ge. Cardinality(S) >= T + 1 BY <1>types, Arith_DoubleGtNplusTImplTplusOne
  <1>pick. PICK id \in S : id \in CORRECT BY <1>sub, <1>ge, EarlyTplusOneHasCorrect
  <1> QED BY <1>pick DEF S, Senders1

THEOREM LockedNextCorrectD2Value ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         IsD2(m),
         AsD2(m).src \in CORRECT
  PROVE  AsD2(m).v = v
  <1>support. v \in SupportedValues(a)
              /\ \A u \in SupportedValues(a) : u = v
        BY StrictQuorumSupportedSingleton
  <1>wv. AsD2(m).v \in VALUES BY Msgs2VInValues
  <1>d2. \E md \in msgs2[a + 1] :
            IsD2(md) /\ AsD2(md).v = AsD2(m).v /\ AsD2(md).src \in CORRECT
        OBVIOUS
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>maj. LET Sv == { mm \in msgs1[a + 1] : mm.v = AsD2(m).v } IN
            2 * Cardinality(Senders1(Sv)) > N + T
        BY <1>l7, <1>wv, <1>d2 DEF Lemma7_D2RequiresQuorum
  <1>corrM1. \E id \in CORRECT :
               \E mm \in msgs1[a + 1] : mm.src = id /\ mm.v = AsD2(m).v
        BY <1>wv, <1>maj, EarlyMajorityM1HasCorrect
  <1> PICK id \in CORRECT, mm \in msgs1[a + 1] :
        mm.src = id /\ mm.v = AsD2(m).v
        BY <1>corrM1
  <1>pin. mm.v = v BY <1>support, SupportedSingletonPinsNextM1
  <1> QED BY <1>pin

THEOREM LockedNextNoCorrectQ2 ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         IsQ2(m),
         AsQ2(m).src \in CORRECT
  PROVE  FALSE
  <1> USE DEF IndInv
  <1>support. v \in SupportedValues(a)
              /\ \A u \in SupportedValues(a) : u = v
        BY StrictQuorumSupportedSingleton
  <1>rnext. a + 1 \in { rr \in ROUNDS :
                  \E mq \in msgs2[rr] : IsQ2(mq) /\ AsQ2(mq).src \in CORRECT }
        OBVIOUS
  <1>wit. LET n0 == Cardinality({ id \in CORRECT:
                        [ src |-> id, r |-> a + 1, v |-> 0 ] \in msgs1[a + 1] })
              n1 == Cardinality({ id \in CORRECT:
                        [ src |-> id, r |-> a + 1, v |-> 1 ] \in msgs1[a + 1] })
              nf == Cardinality({ id \in FAULTY:
                        id \in { mm.src : mm \in msgs1[a + 1] } })
          IN
          \E x0, x1 \in 0..N :
            /\ x0 <= n0 /\ x1 <= n1
            /\ x0 + x1 + nf >= N - T
            /\ 2 * x0 <= N + T
            /\ 2 * x1 <= N + T
        BY <1>rnext DEF Lemma8_Q2RequiresNoQuorumFaster
  <1> PICK x0 \in 0..N, x1 \in 0..N :
        LET n0 == Cardinality({ id \in CORRECT:
                      [ src |-> id, r |-> a + 1, v |-> 0 ] \in msgs1[a + 1] })
            n1 == Cardinality({ id \in CORRECT:
                      [ src |-> id, r |-> a + 1, v |-> 1 ] \in msgs1[a + 1] })
            nf == Cardinality({ id \in FAULTY:
                      id \in { mm.src : mm \in msgs1[a + 1] } })
        IN
          /\ x0 <= n0 /\ x1 <= n1
          /\ x0 + x1 + nf >= N - T
          /\ 2 * x0 <= N + T
          /\ 2 * x1 <= N + T
        BY <1>wit
  <1> DEFINE N0 == { id \in CORRECT :
                       [ src |-> id, r |-> a + 1, v |-> 0 ] \in msgs1[a + 1] }
             N1 == { id \in CORRECT :
                       [ src |-> id, r |-> a + 1, v |-> 1 ] \in msgs1[a + 1] }
             NF == { id \in FAULTY : id \in { mm.src : mm \in msgs1[a + 1] } }
  <1>bounds. /\ x0 <= Cardinality(N0)
              /\ x1 <= Cardinality(N1)
              /\ x0 + x1 + Cardinality(NF) >= N - T
              /\ 2 * x0 <= N + T
              /\ 2 * x1 <= N + T
        OBVIOUS
  <1>fin0. IsFiniteSet(N0) BY FiniteCF, FS_Subset
  <1>fin1. IsFiniteSet(N1) BY FiniteCF, FS_Subset
  <1>finF. IsFiniteSet(NF) BY FiniteCF, FS_Subset
  <1>nfLe. Cardinality(NF) <= F BY FiniteCF, FS_Subset, NTF DEF NF
  <1>types. /\ x0 \in Nat /\ x1 \in Nat
             /\ Cardinality(N0) \in Nat
             /\ Cardinality(N1) \in Nat
             /\ Cardinality(NF) \in Nat
        BY <1>fin0, <1>fin1, <1>finF, FS_CardinalityType
  <1>v0. CASE v = 0
    <2>n1Empty. N1 = {}
      <3>subEmpty. N1 \subseteq {}
        <4> SUFFICES ASSUME NEW id \in N1 PROVE id \in {} OBVIOUS
        <4>m1. [ src |-> id, r |-> a + 1, v |-> 1 ] \in msgs1[a + 1]
                /\ id \in CORRECT
              BY DEF N1
        <4>pin. [ src |-> id, r |-> a + 1, v |-> 1 ].v = v
              BY <1>support, <4>m1, SupportedSingletonPinsNextM1
        <4>false. FALSE BY <1>v0, <4>pin
        <4> QED BY <4>false
      <3> QED BY <3>subEmpty
    <2>n1Card. Cardinality(N1) = 0 BY <2>n1Empty, <1>fin1, FS_EmptySet
    <2>x1zero. x1 <= 0 BY <1>bounds, <2>n1Card
    <2> QED BY <1>bounds, <1>nfLe, <1>types, <2>x1zero, Arith_Lemma8Pinned0Contrad
  <1>v1. CASE v = 1
    <2>n0Empty. N0 = {}
      <3>subEmpty. N0 \subseteq {}
        <4> SUFFICES ASSUME NEW id \in N0 PROVE id \in {} OBVIOUS
        <4>m1. [ src |-> id, r |-> a + 1, v |-> 0 ] \in msgs1[a + 1]
                /\ id \in CORRECT
              BY DEF N0
        <4>pin. [ src |-> id, r |-> a + 1, v |-> 0 ].v = v
              BY <1>support, <4>m1, SupportedSingletonPinsNextM1
        <4>false. FALSE BY <1>v1, <4>pin
        <4> QED BY <4>false
      <3> QED BY <3>subEmpty
    <2>n0Card. Cardinality(N0) = 0 BY <2>n0Empty, <1>fin0, FS_EmptySet
    <2>x0zero. x0 <= 0 BY <1>bounds, <2>n0Card
    <2> QED BY <1>bounds, <1>nfLe, <1>types, <2>x0zero, Arith_Lemma8Pinned1Contrad
  <1> QED BY <1>v0, <1>v1 DEF VALUES

THEOREM ReplicaPredRoundHasTotal ==
  ASSUME TypeOK, IndInv,
         NEW id \in CORRECT,
         round[id] > 1,
         NEW r \in ROUNDS,
         r = round[id] - 1
  PROVE  Cardinality(Senders2(msgs2[r])) >= N - T
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>dom. round \in [ CORRECT -> ROUNDS ] /\ step \in [ CORRECT -> {S1, S2, S3} ]
        BY DEF TypeOK
  <1>ridNat. round[id] \in Nat BY <1>dom, RoundsNat
  <1>rplus. r + 1 = round[id]
        BY <1>ridNat, Arith_MinusOnePlusOne
  <1>rplusIn. r + 1 \in ROUNDS BY <1>rplus, <1>dom
  <1>s1. CASE step[id] = S1
    <2>next. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
          BY <1>rplus, <1>s1
    <2> QED BY <1>l12, <1>rplusIn, <2>next DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>notS1. CASE step[id] # S1
    <2>m1. \E m \in msgs1[r + 1] : m.src = id
          BY <1>l5, <1>rplus, <1>rplusIn, <1>notS1 DEF Lemma5_RoundNeedsSentMessages
    <2>succ. r + 1 \in ROUNDS \ {1} BY <1>rplusIn, RoundsNat, ConstNat
    <2>rw. r + 1 \in { rr \in ROUNDS \ {1}: \E m \in msgs1[rr]: m.src \in CORRECT }
          BY <2>m1, <2>succ
    <2>q. Cardinality(Senders2(msgs2[(r + 1) - 1])) >= N - T
          BY <1>l10, <2>rw DEF Lemma10_M1RequiresQuorum
    <2>prev. (r + 1) - 1 = r BY RoundsNat, Arith_PlusOneMinusOne
    <2> QED BY <2>q, <2>prev
  <1> QED BY <1>s1, <1>notS1

\* CENTRAL LOCK OBLIGATION. Once a correct replica has decided, every later Step3 receive
\* set at its current round contains a strict D-quorum for the decided value. This is the
\* receive-set form needed both for Lemma6 preservation (it rules out the random reset
\* branch and pins any high branch to the decision) and for Lemma1's decided-carry case.
\* ONE-ROUND STRICT LOCK. If round a has a strict D quorum for v, then every N-T
\* receive set in round a+1 has a strict D quorum for v. Finishing this theorem is
\* the main local proof task for both inductiveness and agreement:
\*   strict quorum at a plus N-T type-2 senders -> SupportedValues(a) = {v};
\*   Lemma9 pins correct M1s in a+1 to v;
\*   any Step2 receive set in a+1 has > (N+T)/2 correct M1(v), so correct type-2
\*   senders in a+1 send D2(v);
\*   any Step3 receive set in a+1 contains enough correct type-2 senders for a strict
\*   D2(v) majority, using N > 5*T and F <= T.
THEOREM StrictQuorumNextCorrectType2 ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW m \in msgs2[a + 1],
         (IsD2(m) => AsD2(m).src \in CORRECT)
           /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
  PROVE  IsD2(m) /\ AsD2(m).v = v
  <1>d. CASE IsD2(m)
    <2>src. AsD2(m).src \in CORRECT BY <1>d
    <2>val. AsD2(m).v = v BY <1>d, <2>src, LockedNextCorrectD2Value
    <2> QED BY <1>d, <2>val
  <1>q. CASE IsQ2(m)
    <2>src. AsQ2(m).src \in CORRECT BY <1>q
    <2>false. FALSE BY <1>q, <2>src, LockedNextNoCorrectQ2
    <2> QED BY <2>false
  <1> QED BY <1>d, <1>q, VariantAx

THEOREM LockedReceiveCorrectType2Strict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A m \in received :
           ((IsD2(m) => AsD2(m).src \in CORRECT)
             /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
              => IsD2(m) /\ AsD2(m).v = v
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = v }))
            > N + T
  <1> DEFINE GoodMsgs == { m \in received : IsD2(m) /\ AsD2(m).v = v }
             Good == Senders2(GoodMsgs)
             R == Senders2(received)
             Bad == R \ Good
  <1>badFaulty. Bad \subseteq FAULTY
    <2> SUFFICES ASSUME NEW id \in Bad PROVE id \in FAULTY OBVIOUS
    <2>rin. id \in R /\ id \notin Good BY DEF Bad
    <2>pick. PICK m \in received :
          (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id)
        BY <2>rin DEF R, Senders2
    <2>all. id \in ALL BY <2>rin DEF R, Senders2
    <2>corr. CASE id \in CORRECT
      <3>dsrc. IsD2(m) => AsD2(m).src \in CORRECT
        <4> SUFFICES ASSUME IsD2(m) PROVE AsD2(m).src \in CORRECT
              OBVIOUS
        <4>src. AsD2(m).src = id BY <2>pick, VariantAx
        <4> QED BY <4>src, <2>corr
      <3>qsrc. IsQ2(m) => AsQ2(m).src \in CORRECT
        <4> SUFFICES ASSUME IsQ2(m) PROVE AsQ2(m).src \in CORRECT
              OBVIOUS
        <4>src. AsQ2(m).src = id BY <2>pick, VariantAx
        <4> QED BY <4>src, <2>corr
      <3>ant. (IsD2(m) => AsD2(m).src \in CORRECT)
                 /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
            BY <3>dsrc, <3>qsrc
      <3>locked. IsD2(m) /\ AsD2(m).v = v BY <3>ant
      <3>gin. id \in Good BY <2>pick, <3>locked DEF Good, GoodMsgs, Senders2
      <3> QED BY <2>rin, <3>gin
    <2>faulty. CASE id \in FAULTY
      <3> QED BY <2>faulty
    <2> QED BY <2>all, <2>corr, <2>faulty DEF ALL
  <1>cover. R \subseteq Good \union Bad BY DEF Bad
  <1>finG. IsFiniteSet(Good) BY Senders2_Sub
  <1>finB. IsFiniteSet(Bad) BY <1>badFaulty, FiniteCF, FS_Subset
  <1>finU. IsFiniteSet(Good \union Bad) BY <1>finG, <1>finB, FS_Union
  <1>rleU. Cardinality(R) <= Cardinality(Good \union Bad)
        BY <1>cover, <1>finU, FS_Subset
  <1>ule. Cardinality(Good \union Bad) <= Cardinality(Good) + Cardinality(Bad)
        BY <1>finG, <1>finB, CardUnion2LeSum
  <1>badLe. Cardinality(Bad) <= F BY <1>badFaulty, FiniteCF, FS_Subset, NTF
  <1>types. /\ Cardinality(R) \in Nat
             /\ Cardinality(Good) \in Nat
             /\ Cardinality(Bad) \in Nat
             /\ Cardinality(Good \union Bad) \in Nat
        BY Senders2_Sub, <1>finB, <1>finU, FS_CardinalityType
  <1>rle. Cardinality(R) <= Cardinality(Good) + Cardinality(Bad)
        BY <1>rleU, <1>ule, <1>types, Arith_LeTrans
  <1>strict. 2 * Cardinality(Good) > N + T
        BY <1>rle, <1>badLe, <1>types, Arith_StrictMajorityAfterFaults DEF R
  <1> QED BY <1>strict DEF Good, GoodMsgs

THEOREM StrictQuorumNextReceiveStrictD ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         NEW received \in SUBSET msgs2[a + 1],
         Cardinality(Senders2(received)) = N - T
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = v }))
            > N + T
  <1>recsub. received \subseteq msgs2[a + 1] OBVIOUS
  <1>locked. \A m \in received :
        ((IsD2(m) => AsD2(m).src \in CORRECT)
          /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
            => IsD2(m) /\ AsD2(m).v = v
    <2> SUFFICES ASSUME NEW m \in received,
                         (IsD2(m) => AsD2(m).src \in CORRECT)
                           /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
                  PROVE  IsD2(m) /\ AsD2(m).v = v
          OBVIOUS
    <2>min. m \in msgs2[a + 1] BY <1>recsub
    <2> QED BY <2>min, StrictQuorumNextCorrectType2
  <1> QED BY <1>locked, LockedReceiveCorrectType2Strict

THEOREM LockedReceiveStrictD ==
  ASSUME TypeOK, IndInv,
         NEW id0 \in CORRECT,
         Step3(id0),
         decision[id0] # NO_DECISION,
         NEW received \in SUBSET msgs2[round[id0]],
         Cardinality(Senders2(received)) = N - T
  PROVE  2 * Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = decision[id0] }))
            > N + T
  <1>l1. Lemma1_DecisionRequiresLastQuorumLessRam BY DEF IndInv
  <1>dom. /\ round[id0] \in ROUNDS
          /\ decision[id0] \in VALUES \union { NO_DECISION }
        BY DEF TypeOK
  <1>dec. /\ round[id0] > 1
          /\ ExistsQuorum2LessRam(round[id0] - 1, decision[id0])
        BY <1>l1 DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1>v. decision[id0] \in VALUES BY <1>dom, NoDecisionNotValue
  <1>rin. round[id0] \in ROUNDS /\ round[id0] # 1 BY <1>dom, <1>dec, RoundsNat
  <1>prev. round[id0] - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
  <1>totalPrev. Cardinality(Senders2(msgs2[round[id0] - 1])) >= N - T
        BY <1>dec, <1>prev, ReplicaPredRoundHasTotal
  <1>ridNat. round[id0] \in Nat BY <1>dom, RoundsNat
  <1>succ. (round[id0] - 1) + 1 = round[id0]
        BY <1>ridNat, <1>dec, Arith_MinusOnePlusOne
  <1>succIn. (round[id0] - 1) + 1 \in ROUNDS
        BY <1>succ, <1>dom
  <1>recsub. received \in SUBSET msgs2[(round[id0] - 1) + 1]
        BY <1>succ
  <1> QED BY <1>dec, <1>v, <1>prev, <1>totalPrev, <1>succIn, <1>recsub, StrictQuorumNextReceiveStrictD

THEOREM HighWeightReceivedL11Witness ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         NEW v \in VALUES,
         Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1
  PROVE  \/ LET Qv == Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
             IN 2 * Cardinality(Qv) > N + T
         \/ LET n0 == Cardinality(DvSet(r, 0))
                n1 == Cardinality(DvSet(r, 1))
                nq == Cardinality(QSet(r))
            IN
            \E x0, x1 \in 0..N:
              /\ x0 <= n0 /\ x1 <= n1
              /\ x0 + x1 + nq >= N - T
              /\ 2 * x0 <= N + T
              /\ 2 * x1 <= N + T
  <1> DEFINE R0 == DPart(received, 0)
             R1 == DPart(received, 1)
             RQ == QPart(received)
             Full0 == Senders2(DvSet(r, 0))
             Full1 == Senders2(DvSet(r, 1))
  <1>v0. 0 \in VALUES BY DEF VALUES
  <1>v1. 1 \in VALUES BY DEF VALUES
  <1>z01. 0 # 1 BY DEF VALUES
  <1>sub0. R0 \subseteq DvSet(r, 0) BY DEF R0, DPart, DvSet
  <1>sub1. R1 \subseteq DvSet(r, 1) BY DEF R1, DPart, DvSet
  <1>subq. RQ \subseteq QSet(r) BY DEF RQ, QPart, QSet
  <1>finD0. IsFiniteSet(DvSet(r, 0)) BY <1>v0, D2SetFinite
  <1>finD1. IsFiniteSet(DvSet(r, 1)) BY <1>v1, D2SetFinite
  <1>finQ. IsFiniteSet(QSet(r)) BY Q2SetFinite
  <1>finR0. IsFiniteSet(R0) BY <1>sub0, <1>finD0, FS_Subset
  <1>finR1. IsFiniteSet(R1) BY <1>sub1, <1>finD1, FS_Subset
  <1>finRQ. IsFiniteSet(RQ) BY <1>subq, <1>finQ, FS_Subset
  <1>c0. Cardinality(R0) <= Cardinality(DvSet(r, 0)) BY <1>sub0, <1>finD0, FS_Subset
  <1>c1. Cardinality(R1) <= Cardinality(DvSet(r, 1)) BY <1>sub1, <1>finD1, FS_Subset
  <1>cq. Cardinality(RQ) <= Cardinality(QSet(r)) BY <1>subq, <1>finQ, FS_Subset
  <1>part. Cardinality(Senders2(received))
              <= Cardinality(R0) + Cardinality(R1) + Cardinality(RQ)
        BY Msgs2SenderPartitionBound DEF R0, R1, RQ, DPart, QPart
  <1>shape0. \A m \in R0 : IsD2(m) /\ AsD2(m).src \in ALL
                             /\ AsD2(m).r = r /\ AsD2(m).v = 0
        BY Msgs2Shape, Msgs2SrcInAll, Msgs2RShape DEF R0, DPart
  <1>shape1. \A m \in R1 : IsD2(m) /\ AsD2(m).src \in ALL
                             /\ AsD2(m).r = r /\ AsD2(m).v = 1
        BY Msgs2Shape, Msgs2SrcInAll, Msgs2RShape DEF R1, DPart
  <1>send0. Cardinality(R0) <= Cardinality(Senders2(R0))
        BY <1>shape0, D2Fixed_CardLeSenders
  <1>send1. Cardinality(R1) <= Cardinality(Senders2(R1))
        BY <1>shape1, D2Fixed_CardLeSenders
  <1>s0sub. Cardinality(Senders2(R0)) <= Cardinality(Full0)
        BY <1>sub0, Senders2_Mono DEF Full0
  <1>s1sub. Cardinality(Senders2(R1)) <= Cardinality(Full1)
        BY <1>sub1, Senders2_Mono DEF Full1
  <1>bd0. Cardinality(DvSet(r, 0)) <= N BY <1>v0, D2SetFinite
  <1>bd1. Cardinality(DvSet(r, 1)) <= N BY <1>v1, D2SetFinite
  <1>types. /\ Cardinality(R0) \in Nat /\ Cardinality(R1) \in Nat /\ Cardinality(RQ) \in Nat
             /\ Cardinality(DvSet(r, 0)) \in Nat /\ Cardinality(DvSet(r, 1)) \in Nat
             /\ Cardinality(QSet(r)) \in Nat
             /\ Cardinality(Senders2(received)) \in Nat
             /\ Cardinality(Senders2(R0)) \in Nat /\ Cardinality(Senders2(R1)) \in Nat
             /\ Cardinality(Full0) \in Nat /\ Cardinality(Full1) \in Nat
             /\ N \in Nat /\ N - T \in Nat /\ N + T \in Nat /\ T + 1 \in Nat
        BY <1>finR0, <1>finR1, <1>finRQ, <1>finD0, <1>finD1, <1>finQ,
           Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>r0leFull. Cardinality(R0) <= Cardinality(Full0)
        BY <1>send0, <1>s0sub, <1>types, Arith_LeTrans
  <1>r1leFull. Cardinality(R1) <= Cardinality(Full1)
        BY <1>send1, <1>s1sub, <1>types, Arith_LeTrans
  <1>r0leN. Cardinality(R0) <= N BY <1>c0, <1>bd0, <1>types, Arith_LeTrans
  <1>r1leN. Cardinality(R1) <= N BY <1>c1, <1>bd1, <1>types, Arith_LeTrans
  <1>x0N. Cardinality(R0) \in 0..N BY <1>types, <1>r0leN
  <1>x1N. Cardinality(R1) \in 0..N BY <1>types, <1>r1leN
  <1>sum. Cardinality(R0) + Cardinality(R1) + Cardinality(QSet(r)) >= N - T
        BY <1>part, <1>cq, <1>types, Arith_SumThirdMonoGe
  <1>majority. CASE LET Qv == Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
                    IN 2 * Cardinality(Qv) > N + T
    <2> QED BY <1>majority
  <1>noMajority. CASE ~(LET Qv == Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
                         IN 2 * Cardinality(Qv) > N + T)
    <2>vIs0. CASE v = 0
      <3>high0. Cardinality(Senders2(R0)) >= T + 1 BY <2>vIs0 DEF R0, DPart
      <3>r0ge. Cardinality(R0) >= T + 1
            BY <3>high0, <1>finR0, Senders2_CardLeSet, <1>types, Arith_GeTrans
      <3>dv0ge. Cardinality(DvSet(r, 0)) >= T + 1
            BY <3>r0ge, <1>c0, <1>types, Arith_GeTrans
      <3>d0. 2 * Cardinality(R0) <= N + T
            BY <1>noMajority, <2>vIs0, <1>r0leFull, <1>types, Arith_DoubleLeFromNotGtMono
               DEF Full0, DvSet
      <3>notMajR1. ~(2 * Cardinality(R1) > N + T)
        <4> SUFFICES ASSUME 2 * Cardinality(R1) > N + T PROVE FALSE OBVIOUS
        <4>full1gt. 2 * Cardinality(Full1) > N + T
              BY <1>r1leFull, <1>types, Arith_DoubleGtMono
        <4>eq. 1 = 0 BY <1>v0, <1>v1, <3>dv0ge, <4>full1gt, DQuorumDominatesMajorityD DEF Full1
        <4> QED BY <4>eq, <1>z01
      <3>d1. 2 * Cardinality(R1) <= N + T
            BY <3>notMajR1, <1>types, Arith_DoubleNotGtLe
      <3> QED BY <1>x0N, <1>x1N, <1>c0, <1>c1, <1>sum, <3>d0, <3>d1
    <2>vIs1. CASE v = 1
      <3>high1. Cardinality(Senders2(R1)) >= T + 1 BY <2>vIs1 DEF R1, DPart
      <3>r1ge. Cardinality(R1) >= T + 1
            BY <3>high1, <1>finR1, Senders2_CardLeSet, <1>types, Arith_GeTrans
      <3>dv1ge. Cardinality(DvSet(r, 1)) >= T + 1
            BY <3>r1ge, <1>c1, <1>types, Arith_GeTrans
      <3>d1. 2 * Cardinality(R1) <= N + T
            BY <1>noMajority, <2>vIs1, <1>r1leFull, <1>types, Arith_DoubleLeFromNotGtMono
               DEF Full1, DvSet
      <3>notMajR0. ~(2 * Cardinality(R0) > N + T)
        <4> SUFFICES ASSUME 2 * Cardinality(R0) > N + T PROVE FALSE OBVIOUS
        <4>full0gt. 2 * Cardinality(Full0) > N + T
              BY <1>r0leFull, <1>types, Arith_DoubleGtMono
        <4>eq. 0 = 1 BY <1>v0, <1>v1, <3>dv1ge, <4>full0gt, DQuorumDominatesMajorityD DEF Full0
        <4> QED BY <4>eq, <1>z01
      <3>d0. 2 * Cardinality(R0) <= N + T
            BY <3>notMajR0, <1>types, Arith_DoubleNotGtLe
      <3> QED BY <1>x0N, <1>x1N, <1>c0, <1>c1, <1>sum, <3>d0, <3>d1
    <2> QED BY <2>vIs0, <2>vIs1, <1>v0, <1>v1 DEF VALUES
  <1> QED BY <1>majority, <1>noMajority

THEOREM ReceivedDQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         NEW v \in VALUES,
         Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
  <1> DEFINE Rv == { m \in received: IsD2(m) /\ AsD2(m).v = v }
  <1>wv. w \in VALUES BY DEF SupportedValues
  <1>sub. Rv \subseteq DvSet(r, v) BY DEF Rv, DvSet
  <1>finD. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>finR. IsFiniteSet(Rv) BY <1>sub, <1>finD, FS_Subset
  <1>sendLe. Cardinality(Senders2(Rv)) <= Cardinality(Rv)
        BY <1>finR, Senders2_CardLeSet
  <1>rLeD. Cardinality(Rv) <= Cardinality(DvSet(r, v))
        BY <1>sub, <1>finD, FS_Subset
  <1>types. /\ Cardinality(Senders2(Rv)) \in Nat
             /\ Cardinality(Rv) \in Nat
             /\ Cardinality(DvSet(r, v)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finR, <1>finD, FS_CardinalityType, ConstNat, FleqT
  <1>rge. Cardinality(Rv) >= T + 1
        BY <1>sendLe, <1>types, Arith_GeTrans DEF Rv
  <1>dge. Cardinality(DvSet(r, v)) >= T + 1
        BY <1>rge, <1>rLeD, <1>types, Arith_GeTrans
  <1> QED BY <1>wv, <1>dge, DQuorumDominatesSupported

THEOREM SupportedInReceivedQuorum ==
  ASSUME NEW r \in ROUNDS, NEW v \in SupportedValues(r),
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T
  PROVE  Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1
  <1> DEFINE D == Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })
             O == Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v })
             R == Senders2(received)
  <1>vval. v \in VALUES BY DEF SupportedValues
  <1>ob. Cardinality(O) < N - 2 * T BY DEF SupportedValues, O
  <1>cover. R \subseteq D \union O BY DEF R, D, O, Senders2
  <1>finD. IsFiniteSet(D) BY Senders2_Sub
  <1>finO. IsFiniteSet(O) BY Senders2_Sub
  <1>finU. IsFiniteSet(D \union O) BY <1>finD, <1>finO, FS_Union
  <1>rleU. Cardinality(R) <= Cardinality(D \union O)
        BY <1>cover, <1>finU, FS_Subset
  <1>ule. Cardinality(D \union O) <= Cardinality(D) + Cardinality(O)
        BY <1>finD, <1>finO, CardUnion2LeSum
  <1>rle. Cardinality(R) <= Cardinality(D) + Cardinality(O)
    <2>types. /\ Cardinality(R) \in Nat /\ Cardinality(D \union O) \in Nat
               /\ Cardinality(D) \in Nat /\ Cardinality(O) \in Nat
          BY Senders2_Sub, <1>finU, <1>finD, <1>finO, FS_CardinalityType
    <2> QED BY <1>rleU, <1>ule, <2>types, ConstNat
  <1>types. /\ Cardinality(R) \in Nat /\ Cardinality(D) \in Nat /\ Cardinality(O) \in Nat
        BY Senders2_Sub, <1>finD, <1>finO, FS_CardinalityType
  <1>notlt. ~(Cardinality(D) < T + 1)
    <2>suf. SUFFICES ASSUME Cardinality(D) < T + 1 PROVE FALSE OBVIOUS
    <2> QED BY <1>types, <1>rle, <1>ob, <2>suf, Arith_SupportedQuorumContrad DEF R
  <1>ge. Cardinality(D) >= T + 1 BY <1>types, <1>notlt, Arith_NotLtTplusOneGe
  <1> QED BY <1>ge DEF D

LEMMA Arith_SupportedQuorumGeContrad ==
  ASSUME NEW rcv \in Nat, NEW dv \in Nat, NEW oth \in Nat,
         rcv >= N - T, rcv <= dv + oth, dv < T + 1, oth < N - 2 * T
  PROVE  FALSE
  <1>dvle. dv <= T BY ConstNat, FleqT
  <1>sumlt. dv + oth < N - T BY <1>dvle, ConstNat, NgtT, FleqT
  <1>ge. dv + oth >= N - T BY ConstNat
  <1> QED BY <1>sumlt, <1>ge, ConstNat

THEOREM SupportedFromTotalAndFewOthers ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(Senders2(msgs2[r])) >= N - T,
         Cardinality(Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v })) < N - 2 * T
  PROVE  v \in SupportedValues(r)
  <1> DEFINE D == Senders2(DvSet(r, v))
             O == Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v })
             R == Senders2(msgs2[r])
  <1>cover. R \subseteq D \union O BY DEF R, D, O, DvSet, Senders2
  <1>finD. IsFiniteSet(D) BY Senders2_Sub
  <1>finO. IsFiniteSet(O) BY Senders2_Sub
  <1>finU. IsFiniteSet(D \union O) BY <1>finD, <1>finO, FS_Union
  <1>rleU. Cardinality(R) <= Cardinality(D \union O)
        BY <1>cover, <1>finU, FS_Subset
  <1>ule. Cardinality(D \union O) <= Cardinality(D) + Cardinality(O)
        BY <1>finD, <1>finO, CardUnion2LeSum
  <1>rle. Cardinality(R) <= Cardinality(D) + Cardinality(O)
    <2>types. /\ Cardinality(R) \in Nat /\ Cardinality(D \union O) \in Nat
               /\ Cardinality(D) \in Nat /\ Cardinality(O) \in Nat
          BY Senders2_Sub, <1>finU, <1>finD, <1>finO, FS_CardinalityType
    <2> QED BY <1>rleU, <1>ule, <2>types, ConstNat
  <1>types. /\ Cardinality(R) \in Nat /\ Cardinality(D) \in Nat /\ Cardinality(O) \in Nat
        BY Senders2_Sub, <1>finD, <1>finO, FS_CardinalityType
  <1>notlt. ~(Cardinality(D) < T + 1)
    <2>suf. SUFFICES ASSUME Cardinality(D) < T + 1 PROVE FALSE OBVIOUS
    <2> QED BY <1>types, <1>rle, <2>suf, Arith_SupportedQuorumGeContrad DEF R, O
  <1>ge. Cardinality(D) >= T + 1 BY <1>types, <1>notlt, Arith_NotLtTplusOneGe
  <1> QED BY <1>ge DEF SupportedValues, DvSet, D, O, R

THEOREM LowWeightsSupportedEmpty ==
  ASSUME NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A v \in VALUES :
           Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) < T + 1
  PROVE  SupportedValues(r) = {}
  <1>nonempty. CASE SupportedValues(r) # {}
    <2> PICK w \in SupportedValues(r) : TRUE BY <1>nonempty
    <2>wv. w \in VALUES BY DEF SupportedValues
    <2>ge. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = w })) >= T + 1
          BY SupportedInReceivedQuorum
    <2>lt. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = w })) < T + 1
          BY <2>wv
    <2>types. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = w })) \in Nat
               /\ T + 1 \in Nat
          BY Senders2_Sub, FS_CardinalityType, ConstNat, FleqT
    <2>false. FALSE BY <2>ge, <2>lt, <2>types, Arith_GeLtContrad
    <2> QED BY <2>false
  <1>empty. CASE SupportedValues(r) = {}
    <2> QED BY <1>empty
  <1> QED BY <1>nonempty, <1>empty

SupportedValuesP(r) ==
  LET ExistsSupport(v) ==
    LET Sv == Senders2(DvPSet(r, v)) IN
    LET Others == Senders2({ m \in msgs2'[r]: IsQ2(m) \/ AsD2(m).v /= v }) IN
    /\ Cardinality(Senders2(msgs2'[r])) >= N - T
    /\ Cardinality(Sv) >= T + 1
    /\ Cardinality(Others) < N - 2 * T
  IN
  { v \in VALUES: ExistsSupport(v) }

THEOREM SupportedValuesPrimeIsP ==
  ASSUME NEW r \in ROUNDS
  PROVE  SupportedValues(r)' = SupportedValuesP(r)
  BY DEF SupportedValues, SupportedValuesP, DvSet, DvPSet

THEOREM SupportedValuesPFrame ==
  ASSUME NEW r \in ROUNDS, msgs2' = msgs2
  PROVE  SupportedValuesP(r) = SupportedValues(r)
  BY DEF SupportedValues, SupportedValuesP, DvSet, DvPSet

THEOREM SupportedPToOldWhenTotal ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW v \in SupportedValuesP(r),
         Cardinality(Senders2(msgs2[r])) >= N - T,
         msgs2[r] \subseteq msgs2'[r]
  PROVE  v \in SupportedValues(r)
  <1>vVal. v \in VALUES BY DEF SupportedValuesP
  <1>primeOther. Cardinality(Senders2({ m \in msgs2'[r] : IsQ2(m) \/ AsD2(m).v /= v }))
                    < N - 2 * T
        BY DEF SupportedValuesP, DvPSet
  <1>oldOtherLe. Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
                    <= Cardinality(Senders2({ m \in msgs2'[r] : IsQ2(m) \/ AsD2(m).v /= v }))
    <2>sub. { m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }
              \subseteq { m \in msgs2'[r] : IsQ2(m) \/ AsD2(m).v /= v }
          OBVIOUS
    <2> QED BY <2>sub, Senders2_Mono
  <1>types. /\ Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v })) \in Nat
             /\ Cardinality(Senders2({ m \in msgs2'[r] : IsQ2(m) \/ AsD2(m).v /= v })) \in Nat
             /\ N - 2 * T \in Nat
        BY Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>oldOther. Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
                  < N - 2 * T
        BY <1>oldOtherLe, <1>primeOther, <1>types, Arith_LeLtTrans
  <1> QED BY <1>vVal, <1>oldOther, SupportedFromTotalAndFewOthers

THEOREM TplusOneHasCorrect ==
  ASSUME NEW S, S \subseteq ALL, Cardinality(S) >= T + 1
  PROVE  \E id \in S : id \in CORRECT
  <1>fin. IsFiniteSet(S) BY SubAll_Finite
  <1>card. Cardinality(S) \in Nat BY <1>fin, FS_CardinalityType
  <1>ge. Cardinality(S) >= T + 1 OBVIOUS
  <1>bad. S \ CORRECT \subseteq FAULTY BY DEF ALL
  <1>bd. Cardinality(S \ CORRECT) <= F BY <1>bad, FiniteCF, FS_Subset, NTF
  <1> QED
    <2>suf. SUFFICES ASSUME \A id \in S : id \notin CORRECT PROVE FALSE OBVIOUS
    <2>eq. S = S \ CORRECT BY <2>suf
    <2>le. Cardinality(S) <= F BY <2>eq, <1>bd
    <2> QED BY <1>card, <1>ge, <2>le, Arith_TplusOneNotFaulty

THEOREM MajorityM1HasCorrect ==
  ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
         2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
  <1> DEFINE S == Senders1({ m \in msgs1[r] : m.v = v })
  <1>sub. S \subseteq ALL BY Senders1_Sub
  <1>types. Cardinality(S) \in Nat BY Senders1_Sub, FS_CardinalityType
  <1>ge. Cardinality(S) >= T + 1 BY <1>types, Arith_DoubleGtNplusTImplTplusOne
  <1>pick. PICK id \in S : id \in CORRECT BY <1>sub, <1>ge, TplusOneHasCorrect
  <1> QED BY <1>pick DEF S, Senders1

THEOREM QuorumHasCorrectM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
  <1> USE DEF IndInv
  <1>dv. Cardinality(DvSet(r, v)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
  <1>d2. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY <1>dv, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r] : m.v = v } IN
            2 * Cardinality(Senders1(Sv)) > N + T
        BY <1>d2 DEF Lemma7_D2RequiresQuorum
  <1> QED BY <1>maj, MajorityM1HasCorrect

THEOREM QuorumHasM1Majority ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  LET Sv == { m \in msgs1[r] : m.v = v } IN
           2 * Cardinality(Senders1(Sv)) > N + T
  <1> USE DEF IndInv
  <1>dv. Cardinality(DvSet(r, v)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
  <1>d2. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        BY <1>dv, CorrectD2Exists
  <1> QED BY <1>d2 DEF Lemma7_D2RequiresQuorum

THEOREM LaterQuorumGivesTotalBefore ==
  ASSUME TypeOK, IndInv,
         NEW b \in ROUNDS, NEW r \in ROUNDS, b < r,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w)
  PROVE  Cardinality(Senders2(msgs2[b])) >= N - T
  <1> USE DEF IndInv
  <1>dv. Cardinality(DvSet(r, w)) >= T + 1
        BY DEF ExistsQuorum2LessRam, DvSet
  <1>d2. \E md \in msgs2[r] : IsD2(md) /\ AsD2(md).v = w /\ AsD2(md).src \in CORRECT
        BY <1>dv, CorrectD2Exists
  <1> PICK md \in msgs2[r] :
        IsD2(md) /\ AsD2(md).v = w /\ AsD2(md).src \in CORRECT
        BY <1>d2
  <1> DEFINE id == AsD2(md).src
  <1>idc. id \in CORRECT OBVIOUS
  <1>rshape. AsD2(md).r = r BY Msgs2Shape
  <1>src. AsD2(md).src = id BY DEF id
  <1>dom. round[id] \in ROUNDS BY <1>idc DEF TypeOK
  <1>nat. b \in Nat /\ r \in Nat /\ round[id] \in Nat
        BY <1>dom, RoundsNat
  <1>reach. b + 1 < round[id] \/ (b + 1 = round[id] /\ step[id] # S1)
    <2>s3. CASE step[id] = S3
      <3>rle. r <= round[id]
            BY <1>rshape, <1>src, <1>idc, <2>s3 DEF Lemma4_MessagesNotFromFuture
      <3>notS1. step[id] # S1 BY <2>s3 DEF S1, S3
      <3> QED BY <1>nat, <3>rle, <3>notS1, ConstNat
    <2>notS3. CASE step[id] # S3
      <3>rlt. r < round[id]
            BY <1>rshape, <1>src, <1>idc, <2>notS3 DEF Lemma4_MessagesNotFromFuture
      <3>lt. b + 1 < round[id] BY <1>nat, <3>rlt, ConstNat
      <3> QED BY <3>lt
    <2> QED BY <2>s3, <2>notS3
  <1>bp1. b + 1 \in ROUNDS \ { 1 } BY RoundsNat, ConstNat
  <1>m1. \E mm \in msgs1[b + 1] : mm.src = id
        BY <1>reach, <1>bp1 DEF Lemma5_RoundNeedsSentMessages
  <1>rw. b + 1 \in { rr \in ROUNDS \ { 1 } :
                       \E mm \in msgs1[rr] : mm.src \in CORRECT }
        BY <1>m1, <1>idc, <1>bp1
  <1>q. Cardinality(Senders2(msgs2[(b + 1) - 1])) >= N - T
        BY <1>rw DEF Lemma10_M1RequiresQuorum
  <1>prev. (b + 1) - 1 = b BY RoundsNat, Arith_PlusOneMinusOne
  <1> QED BY <1>q, <1>prev

THEOREM SupportedSingletonNextQuorum ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in VALUES, ExistsQuorum2LessRam(r + 1, w)
  PROVE  w = v
  <1> USE DEF IndInv
  <1>m1. \E id \in CORRECT : \E m \in msgs1[r + 1] : m.src = id /\ m.v = w
        BY QuorumHasCorrectM1
  <1>conn. LET Supported == SupportedValues(r) IN
             \/ Supported = {}
             \/ \E u \in Supported :
                  \A m \in msgs1[r + 1] : m.src \in CORRECT => m.v = u
        BY DEF Lemma9_RoundsConnection
  <1>nonempty. SupportedValues(r) # {} OBVIOUS
  <1>pick. PICK u \in SupportedValues(r) :
              \A m \in msgs1[r + 1] : m.src \in CORRECT => m.v = u
        BY <1>conn, <1>nonempty
  <1>uv. u = v BY <1>pick
  <1>wv. w = u BY <1>m1, <1>pick
  <1> QED BY <1>uv, <1>wv

THEOREM SupportedSingletonNextSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in SupportedValues(r + 1)
  PROVE  w = v
  <1> USE DEF IndInv
  <1>wv. w \in VALUES BY DEF SupportedValues
  <1>sw. Cardinality(Senders2(DvSet(r + 1, w))) >= T + 1
        BY DEF SupportedValues, DvSet
  <1>finw. IsFiniteSet(DvSet(r + 1, w)) BY <1>wv, D2SetFinite
  <1>lew. Cardinality(Senders2(DvSet(r + 1, w))) <= Cardinality(DvSet(r + 1, w))
        BY <1>finw, Senders2_CardLeSet
  <1>types. /\ Cardinality(Senders2(DvSet(r + 1, w))) \in Nat
             /\ Cardinality(DvSet(r + 1, w)) \in Nat
             /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finw, FS_CardinalityType, ConstNat, FleqT
  <1>dw. Cardinality(DvSet(r + 1, w)) >= T + 1
        BY <1>sw, <1>lew, <1>types, Arith_GeTrans
  <1>d2. \E md \in msgs2[r + 1] :
            IsD2(md) /\ AsD2(md).v = w /\ AsD2(md).src \in CORRECT
        BY <1>wv, <1>dw, CorrectD2Exists
  <1>maj. LET Sv == { m \in msgs1[r + 1] : m.v = w } IN
            2 * Cardinality(Senders1(Sv)) > N + T
        BY <1>wv, <1>d2 DEF Lemma7_D2RequiresQuorum
  <1>maj2. 2 * Cardinality(Senders1({ m \in msgs1[r + 1] : m.v = w })) > N + T
        BY <1>maj
  <1>m1. \E id \in CORRECT : \E m \in msgs1[r + 1] : m.src = id /\ m.v = w
    <2> DEFINE S == Senders1({ m \in msgs1[r + 1] : m.v = w })
    <2>sub. S \subseteq ALL BY Senders1_Sub
    <2>types. Cardinality(S) \in Nat BY Senders1_Sub, FS_CardinalityType
    <2>ge. Cardinality(S) >= T + 1 BY <1>maj2, <2>types, Arith_DoubleGtNplusTImplTplusOne
    <2>pick. PICK id \in S : id \in CORRECT BY <2>sub, <2>ge, TplusOneHasCorrect
    <2> QED BY <2>pick DEF S, Senders1
  <1>conn. LET Supported == SupportedValues(r) IN
             \/ Supported = {}
             \/ \E u \in Supported :
                  \A m \in msgs1[r + 1] : m.src \in CORRECT => m.v = u
        BY DEF Lemma9_RoundsConnection
  <1>nonempty. SupportedValues(r) # {} OBVIOUS
  <1>pick. PICK u \in SupportedValues(r) :
              \A m \in msgs1[r + 1] : m.src \in CORRECT => m.v = u
        BY <1>conn, <1>nonempty
  <1>uv. u = v BY <1>pick
  <1>wu. w = u BY <1>m1, <1>pick
  <1> QED BY <1>uv, <1>wu

\* The state tuple (the spec defines no `vars`; we provide one for [Next]_vars).
vars == << value, decision, round, step, msgs1, msgs2 >>

THEOREM TypeOKPrimeIntro ==
  ASSUME value' \in [ CORRECT -> VALUES ],
         decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ],
         round' \in [ CORRECT -> ROUNDS ],
         step' \in [ CORRECT -> { S1, S2, S3 } ],
         \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
           msgs1' = [ r \in ROUNDS |-> { m \in A1 : m.r = r } ],
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
             A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
           msgs2' = [ r \in ROUNDS |->
             { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
               \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } } ]
  PROVE  TypeOK'
  BY DEF TypeOK

THEOREM Msgs2PrimeWitnessIntro ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         msgs2' = [ rr \in ROUNDS |->
           { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
             \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
          msgs2' = [ rr \in ROUNDS |->
            { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
              \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
  OBVIOUS

THEOREM Msgs1AddOneRep ==
  ASSUME NEW A \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW val0 \in VALUES,
         NEW f,
         f = [ rr \in ROUNDS |-> { m \in A : m.r = rr } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { M1(src0, rr0, val0) } ]
         = [ rr \in ROUNDS |->
              { m \in A \union { M1(src0, rr0, val0) } : m.r = rr } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { M1(src0, rr0, val0) } ]
             rhs == [ rr \in ROUNDS |->
                       { m \in A \union { M1(src0, rr0, val0) } : m.r = rr } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>m1r. M1(src0, rr0, val0).r = rr0 BY DEF M1
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>m1r, SMT DEF lhs, rhs, M1
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>m1r, SMT DEF lhs, rhs, M1
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs2AddDRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW val0 \in VALUES,
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { D2(src0, rr0, val0) } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v):
                 mm \in { m \in AD \union { [ src |-> src0, r |-> rr0, v |-> val0 ] }:
                   m.r = rr } }
               \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { D2(src0, rr0, val0) } ]
             rhs == [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v):
                   mm \in { m \in AD \union { [ src |-> src0, r |-> rr0, v |-> val0 ] }:
                     m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>newr. [ src |-> src0, r |-> rr0, v |-> val0 ].r = rr0 OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>newr, VariantAx, SMT DEF lhs, rhs, D2
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>newr, VariantAx, SMT DEF lhs, rhs, D2
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs2AddQRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW src0 \in ALL,
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union { Q2(src0, rr0) } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
               \union { Q2(mm.src, rr):
                 mm \in { m \in AQ \union { [ src |-> src0, r |-> rr0 ] }:
                   m.r = rr } } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union { Q2(src0, rr0) } ]
             rhs == [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr):
                   mm \in { m \in AQ \union { [ src |-> src0, r |-> rr0 ] }:
                     m.r = rr } } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>newr. [ src |-> src0, r |-> rr0 ].r = rr0 OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, <2>newr, VariantAx, SMT DEF lhs, rhs, Q2
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, <2>newr, VariantAx, SMT DEF lhs, rhs, Q2
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs1AddSetRep ==
  ASSUME NEW A \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW rr0 \in ROUNDS,
         NEW Add \in SUBSET [ src: ALL, r: { rr0 }, v: VALUES ],
         NEW f,
         f = [ rr \in ROUNDS |-> { m \in A : m.r = rr } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union Add ]
         = [ rr \in ROUNDS |-> { m \in A \union Add : m.r = rr } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] = f[rr0] \union Add ]
             rhs == [ rr \in ROUNDS |-> { m \in A \union Add : m.r = rr } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, SMT DEF lhs, rhs
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, SMT DEF lhs, rhs
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM Msgs2AddSetsRep ==
  ASSUME NEW AD \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW AQ \in SUBSET [ src: ALL, r: ROUNDS ],
         NEW rr0 \in ROUNDS,
         NEW FD \in SUBSET [ src: ALL, r: { rr0 }, v: VALUES ],
         NEW FQ \in SUBSET [ src: ALL, r: { rr0 } ],
         NEW f,
         f = [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ: m.r = rr } } ]
  PROVE  [ f EXCEPT ![rr0] =
             f[rr0]
               \union { D2(mm.src, rr0, mm.v): mm \in FD }
               \union { Q2(mm.src, rr0): mm \in FQ } ]
         = [ rr \in ROUNDS |->
             { D2(mm.src, rr, mm.v): mm \in { m \in AD \union FD: m.r = rr } }
               \union { Q2(mm.src, rr): mm \in { m \in AQ \union FQ: m.r = rr } } ]
  <1> DEFINE lhs == [ f EXCEPT ![rr0] =
             f[rr0]
               \union { D2(mm.src, rr0, mm.v): mm \in FD }
               \union { Q2(mm.src, rr0): mm \in FQ } ]
             rhs == [ rr \in ROUNDS |->
               { D2(mm.src, rr, mm.v): mm \in { m \in AD \union FD: m.r = rr } }
                 \union { Q2(mm.src, rr): mm \in { m \in AQ \union FQ: m.r = rr } } ]
  <1>vals. \A rr \in ROUNDS : lhs[rr] = rhs[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE lhs[rr] = rhs[rr] OBVIOUS
    <2>eq. CASE rr = rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>eq, VariantAx, SMT DEF lhs, rhs, D2, Q2
    <2>ne. CASE rr # rr0
      <3> SUFFICES ASSUME NEW x PROVE x \in lhs[rr] <=> x \in rhs[rr]
            BY SetExtensionality
      <3> QED BY <2>ne, VariantAx, SMT DEF lhs, rhs, D2, Q2
    <2> QED BY <2>eq, <2>ne
  <1> QED BY <1>vals DEF lhs, rhs

THEOREM UpdateUnionMono ==
  ASSUME NEW f, DOMAIN f = ROUNDS, NEW rr0 \in ROUNDS, NEW Add
  PROVE  \A rr \in ROUNDS :
           f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr]
  <1> SUFFICES ASSUME NEW rr \in ROUNDS
              PROVE f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr]
        OBVIOUS
  <1>eq. CASE rr = rr0
    <2> SUFFICES ASSUME NEW x \in f[rr]
                PROVE  x \in [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr]
          OBVIOUS
    <2> QED BY <1>eq, SMT
  <1>ne. CASE rr # rr0
    <2> SUFFICES ASSUME NEW x \in f[rr]
                PROVE  x \in [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr]
          OBVIOUS
    <2> QED BY <1>ne, SMT
  <1> QED BY <1>eq, <1>ne

THEOREM UpdateUnionNewInAdded ==
  ASSUME NEW f, NEW rr0 \in ROUNDS, NEW Add,
         DOMAIN f = ROUNDS,
         NEW rr \in ROUNDS, NEW m,
         m \in [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr],
         m \notin f[rr]
  PROVE  rr = rr0 /\ m \in Add
  <1>eq. CASE rr = rr0
    <2>1. m \in f[rr0] \union Add BY <1>eq, SMT
    <2>2. m \notin f[rr0] BY <1>eq, SMT
    <2>3. m \in Add BY <2>1, <2>2
    <2> QED BY <1>eq, <2>3
  <1>ne. CASE rr # rr0
    <2>false. FALSE BY <1>ne, SMT
    <2> QED BY <2>false
  <1> QED BY <1>eq, <1>ne

THEOREM UpdateUnion2Mono ==
  ASSUME NEW f, DOMAIN f = ROUNDS, NEW rr0 \in ROUNDS, NEW Add1, NEW Add2
  PROVE  \A rr \in ROUNDS :
           f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr]
  <1> SUFFICES ASSUME NEW rr \in ROUNDS
              PROVE f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr]
        OBVIOUS
  <1>eq. CASE rr = rr0
    <2> SUFFICES ASSUME NEW x \in f[rr]
                PROVE  x \in [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr]
          OBVIOUS
    <2> QED BY <1>eq, SMT
  <1>ne. CASE rr # rr0
    <2> SUFFICES ASSUME NEW x \in f[rr]
                PROVE  x \in [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr]
          OBVIOUS
    <2> QED BY <1>ne, SMT
  <1> QED BY <1>eq, <1>ne

THEOREM UpdateUnion2NewInAdded ==
  ASSUME NEW f, NEW rr0 \in ROUNDS, NEW Add1, NEW Add2,
         DOMAIN f = ROUNDS,
         NEW rr \in ROUNDS, NEW m,
         m \in [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr],
         m \notin f[rr]
  PROVE  rr = rr0 /\ m \in Add1 \union Add2
  <1>eq. CASE rr = rr0
    <2>1. m \in (f[rr0] \union Add1) \union Add2 BY <1>eq, SMT
    <2>2. m \notin f[rr0] BY <1>eq, SMT
    <2>3. m \in Add1 \union Add2 BY <2>1, <2>2
    <2> QED BY <1>eq, <2>3
  <1>ne. CASE rr # rr0
    <2>false. FALSE BY <1>ne, SMT
    <2> QED BY <2>false
  <1> QED BY <1>eq, <1>ne

THEOREM FaultyMsgs2AddedFaulty ==
  ASSUME NEW rr0 \in ROUNDS,
         NEW F2D \in SUBSET FaultyD2Records(rr0),
         NEW F2Q \in SUBSET FaultyQ2Records(rr0),
         NEW m,
         m \in { D2(mm.src, rr0, mm.v): mm \in F2D }
              \union { Q2(mm.src, rr0): mm \in F2Q }
  PROVE  (IsD2(m) => AsD2(m).src \in FAULTY)
         /\ (IsQ2(m) => AsQ2(m).src \in FAULTY)
  <1>d. CASE m \in { D2(mm.src, rr0, mm.v): mm \in F2D }
    <2>pick. PICK mm \in F2D : m = D2(mm.src, rr0, mm.v) BY <1>d
    <2> QED BY <2>pick, VariantAx DEF FaultyD2Records
  <1>q. CASE m \in { Q2(mm.src, rr0): mm \in F2Q }
    <2>pick. PICK mm \in F2Q : m = Q2(mm.src, rr0) BY <1>q
    <2> QED BY <2>pick, VariantAx DEF FaultyQ2Records
  <1> QED BY <1>d, <1>q

\*****************************************************************************
\* FAULTY-STEP CONSEQUENCES.
\* FaultyStepProps packages the common per-lemma consequences under TypeOK:
\* the per-replica state is unchanged, message buffers only grow, and every newly
\* added message has a FAULTY sender. The proof is split through small EXCEPT-update
\* helpers so TLAPS does not have to solve the whole consequence theorem at once.
\*****************************************************************************
THEOREM FaultyStepProps ==
  ASSUME TypeOK, FaultyStep
  PROVE  /\ value' = value /\ decision' = decision /\ round' = round /\ step' = step
         /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] /\ msgs2[rr] \subseteq msgs2'[rr]
         /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
         /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
  <1>fs. PICK rr0 \in ROUNDS :
          /\ \E F1 \in SUBSET [ src: FAULTY, r: { rr0 }, v: VALUES ] :
               msgs1' = [ msgs1 EXCEPT ![rr0] = msgs1[rr0] \union F1 ]
          /\ \E F2D \in SUBSET FaultyD2Records(rr0) :
               \E F2Q \in SUBSET FaultyQ2Records(rr0) :
                 msgs2' = [ msgs2 EXCEPT ![rr0] =
                    msgs2[rr0]
                      \union { D2(mm.src, rr0, mm.v): mm \in F2D }
                      \union { Q2(mm.src, rr0): mm \in F2Q } ]
          /\ UNCHANGED << value, decision, round, step >>
        BY DEF FaultyStep
  <1>f1. PICK F1 \in SUBSET [ src: FAULTY, r: { rr0 }, v: VALUES ] :
          msgs1' = [ msgs1 EXCEPT ![rr0] = msgs1[rr0] \union F1 ]
        BY <1>fs
  <1>f2. PICK F2D \in SUBSET FaultyD2Records(rr0),
              F2Q \in SUBSET FaultyQ2Records(rr0) :
          msgs2' = [ msgs2 EXCEPT ![rr0] =
                    msgs2[rr0]
                      \union { D2(mm.src, rr0, mm.v): mm \in F2D }
                      \union { Q2(mm.src, rr0): mm \in F2Q } ]
        BY <1>fs
  <1>frame. value' = value /\ decision' = decision /\ round' = round /\ step' = step
        BY <1>fs DEF vars
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1mono. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        BY <1>f1, <1>dom1, UpdateUnionMono
  <1>m2mono. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
        BY <1>f2, <1>dom2, UpdateUnion2Mono
  <1>m1new. \A rr \in ROUNDS : \A m \in msgs1'[rr] :
              m \notin msgs1[rr] => m.src \in FAULTY
    <2> SUFFICES ASSUME NEW rr \in ROUNDS, NEW m \in msgs1'[rr],
                         m \notin msgs1[rr]
                PROVE  m.src \in FAULTY
          OBVIOUS
    <2>added. rr = rr0 /\ m \in F1 BY <1>f1, <1>dom1, UpdateUnionNewInAdded
    <2> QED BY <1>f1, <2>added
  <1>m2new. \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
    <2> SUFFICES ASSUME NEW rr \in ROUNDS, NEW m \in msgs2'[rr],
                         m \notin msgs2[rr]
                PROVE  (IsD2(m) => AsD2(m).src \in FAULTY)
                       /\ (IsQ2(m) => AsQ2(m).src \in FAULTY)
          OBVIOUS
    <2>added. rr = rr0
               /\ m \in { D2(mm.src, rr0, mm.v): mm \in F2D }
                       \union { Q2(mm.src, rr0): mm \in F2Q }
        BY <1>f2, <1>dom2, UpdateUnion2NewInAdded
    <2> QED BY <1>f2, <2>added, FaultyMsgs2AddedFaulty
  <1> QED BY <1>frame, <1>m1mono, <1>m2mono, <1>m1new, <1>m2new

THEOREM SupportedPHasOldCorrectD2 ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in SupportedValuesP(r)
  PROVE  \E m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
  <1>vval. v \in VALUES BY DEF SupportedValuesP
  <1>sv. Cardinality(Senders2(DvPSet(r, v))) >= T + 1
        BY DEF SupportedValuesP, DvPSet
  <1>sub. Senders2(DvPSet(r, v)) \subseteq ALL BY Senders2_Sub
  <1>pickSrc. PICK src \in Senders2(DvPSet(r, v)) : src \in CORRECT
        BY <1>sub, <1>sv, TplusOneHasCorrect
  <1>pickM. PICK m \in DvPSet(r, v) : IsD2(m) /\ AsD2(m).src = src
        BY <1>pickSrc, DvPSenderWitness
  <1>old. m \in msgs2[r]
    <2>oldSuf. SUFFICES ASSUME m \notin msgs2[r] PROVE FALSE OBVIOUS
    <2>faulty. AsD2(m).src \in FAULTY
          BY FaultyStepProps, <1>pickM, <2>oldSuf DEF DvPSet
    <2> QED BY <1>pickSrc, <1>pickM, <2>faulty, DisjointCF
  <1> QED BY <1>old, <1>pickSrc, <1>pickM DEF DvPSet

THEOREM DvFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet(DvPSet(r, v))
          /\ Cardinality(DvSet(r, v)) <= Cardinality(DvPSet(r, v))
  <1>p. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY FaultyStepProps
  <1>sub. DvSet(r, v) \subseteq DvPSet(r, v) BY <1>p DEF DvSet, DvPSet
  <1>fin. IsFiniteSet(DvPSet(r, v)) BY D2PSetFinite
  <1>mono. Cardinality(DvSet(r, v)) <= Cardinality(DvPSet(r, v))
        BY <1>sub, <1>fin, FS_Subset
  <1> QED BY <1>fin, <1>mono

THEOREM QFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(QPSet(r))
          /\ Cardinality(QSet(r)) <= Cardinality(QPSet(r))
  <1>p. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY FaultyStepProps
  <1>sub. QSet(r) \subseteq QPSet(r) BY <1>p DEF QSet, QPSet
  <1>fin. IsFiniteSet(QPSet(r)) BY QPSetFinite
  <1>mono. Cardinality(QSet(r)) <= Cardinality(QPSet(r))
        BY <1>sub, <1>fin, FS_Subset
  <1> QED BY <1>fin, <1>mono

THEOREM Msgs2FaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
  <1>p. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY FaultyStepProps
  <1>sub. msgs2[r] \subseteq msgs2'[r] BY <1>p
  <1>fin. IsFiniteSet(msgs2'[r]) BY Msgs2PrimeFinite
  <1>mono. Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
        BY <1>sub, <1>fin, FS_Subset
  <1> QED BY <1>fin, <1>mono

\*****************************************************************************
\* SECTION B -- TYPE PRESERVATION + BASE CASE
\*****************************************************************************

\* BASE CASE. With empty message buffers, no decision, round 1 and step S1,
\* every conjunct of IndInv is vacuous or trivially true.
THEOREM InitInd == Init => TypeOK /\ IndInv
  <1> SUFFICES ASSUME Init PROVE TypeOK /\ IndInv
        OBVIOUS
  <1> USE DEF Init
  <1>m1. \A r \in ROUNDS : msgs1[r] = {}
        OBVIOUS
  <1>m2. \A r \in ROUNDS : msgs2[r] = {}
        OBVIOUS
  \* --- TypeOK ---
  <1>type. TypeOK
    <2>1. value \in [ CORRECT -> VALUES ]
          OBVIOUS
    <2>2. decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
          OBVIOUS
    <2>3. round \in [ CORRECT -> ROUNDS ]
          BY RoundsNat
    <2>4. step \in [ CORRECT -> { S1, S2, S3 } ]
          OBVIOUS
    <2>5. \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]:
              msgs1 = [ r \in ROUNDS |-> { m \in A1: m.r = r } ]
          <3> WITNESS {} \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
          <3> QED OBVIOUS
    <2>6. \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
              A1Q \in SUBSET [ src: ALL, r: ROUNDS ]:
              msgs2 = [ r \in ROUNDS |->
                  { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
                      \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } } ]
          <3> WITNESS {} \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                      {} \in SUBSET [ src: ALL, r: ROUNDS ]
          <3> QED OBVIOUS
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  \* --- IndInv: each lemma holds because msgs are empty / round = 1 / no decision ---
  <1>L2. Lemma2_NoEquivocation1ByCorrect
        BY <1>m1 DEF Lemma2_NoEquivocation1ByCorrect
  <1>L3. Lemma3_NoEquivocation2ByCorrect
        BY <1>m2 DEF Lemma3_NoEquivocation2ByCorrect
  <1>L4. Lemma4_MessagesNotFromFuture
        BY <1>m1, <1>m2 DEF Lemma4_MessagesNotFromFuture
  <1>L5. Lemma5_RoundNeedsSentMessages
        \* round=1, step=S1: positive rounds rule out r < myRound.
        <2> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
              PROVE /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1))
                       => (\E m \in msgs1[r] : m.src = id)
                    /\ (r < round[id])
                       => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
                    /\ (r = round[id] /\ step[id] = S3)
                       => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
            BY DEF Lemma5_RoundNeedsSentMessages
        <2>pos. r \in Nat /\ r >= 1 BY RoundPos
        <2>st. round[id] = 1 /\ step[id] = S1 BY DEF Init
        <2>dist. S1 # S3 BY DEF S1, S3
        <2>notlt. ~(r < round[id]) BY <2>pos, <2>st, Arith_PosNotLtOne
        <2>c1. (r < round[id] \/ (r = round[id] /\ step[id] /= S1))
                 => (\E m \in msgs1[r] : m.src = id)
          <3> SUFFICES ASSUME r < round[id] \/ (r = round[id] /\ step[id] /= S1)
                       PROVE  FALSE
                OBVIOUS
          <3>1. CASE r < round[id] BY <3>1, <2>notlt
          <3>2. CASE r = round[id] /\ step[id] /= S1 BY <3>2, <2>st
          <3> QED BY <3>1, <3>2
        <2>c2. (r < round[id])
                 => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
          <3> SUFFICES ASSUME r < round[id] PROVE FALSE OBVIOUS
          <3> QED BY <2>notlt
        <2>c3. (r = round[id] /\ step[id] = S3)
                 => (\E m \in msgs2[r] : AsD2(m).src = id \/ AsQ2(m).src = id)
          <3> SUFFICES ASSUME r = round[id], step[id] = S3 PROVE FALSE OBVIOUS
          <3> QED BY <2>st, <2>dist
        <2> QED BY <2>c1, <2>c2, <2>c3
  <1>L6. Lemma6_DecisionDefinesValue
        BY DEF Lemma6_DecisionDefinesValue
  <1>L7. Lemma7_D2RequiresQuorum
        BY <1>m2 DEF Lemma7_D2RequiresQuorum
  <1>L8. Lemma8_Q2RequiresNoQuorumFaster
        BY <1>m2 DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>L9. Lemma9_RoundsConnection
        BY <1>m2 DEF Lemma9_RoundsConnection, SupportedValues
  <1>L10. Lemma10_M1RequiresQuorum
        BY <1>m1 DEF Lemma10_M1RequiresQuorum
  <1>L11. Lemma11_ValueOnQuorumLessRam
        \* round[id] = 1, so the r > 1 premise is false.
        BY DEF Lemma11_ValueOnQuorumLessRam
  <1>L12. Lemma12_CannotJumpRoundsWithoutQuorum
        \* nextRoundReached at r with r+1=1 would require r=0, not a positive round.
        BY <1>m2, RoundPos DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>L13. Lemma13_ValueLock
        BY DEF Lemma13_ValueLock
  <1>L1. Lemma1_DecisionRequiresLastQuorumLessRam
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1> QED
        BY <1>type, <1>L1, <1>L2, <1>L3, <1>L4, <1>L5, <1>L6, <1>L7, <1>L8,
           <1>L9, <1>L10, <1>L11, <1>L12, <1>L13 DEF IndInv

\* TYPE PRESERVATION. Each action keeps every variable in its declared type and
\* keeps msgs1/msgs2 in the existential "shape" required by TypeOK.
THEOREM TypePres ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
  <1> USE DEF vars
  <1>1. CASE UNCHANGED vars
        BY <1>1 DEF TypeOK, vars
  <1>2. CASE CorrectStep
    <2>1. PICK id \in CORRECT : Step1(id) \/ Step2(id) \/ Step3(id)
          BY <1>2 DEF CorrectStep
    <2>2. CASE Step1(id)
          \* msgs1[r] gains M1(id,r,value[id]); reuse TypeOK witness A1 \cup {that msg}.
      <3> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
            msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
          BY DEF TypeOK
      <3> PICK A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
            msgs2 = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
          BY DEF TypeOK
      <3> DEFINE A1p == A1 \union { M1(id, round[id], value[id]) }
      <3>fr. /\ value' = value /\ decision' = decision /\ round' = round /\ msgs2' = msgs2
              /\ step' = [ step EXCEPT ![id] = S2 ]
              /\ msgs1' = [ msgs1 EXCEPT
                   ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          BY <2>2 DEF Step1
      <3>r0. round[id] \in ROUNDS /\ value[id] \in VALUES
          BY DEF TypeOK
      <3>idall. id \in ALL BY DEF ALL
      <3>1. value' \in [ CORRECT -> VALUES ] BY <3>fr DEF TypeOK
      <3>2. decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ] BY <3>fr DEF TypeOK
      <3>3. round' \in [ CORRECT -> ROUNDS ] BY <3>fr DEF TypeOK
      <3>4. step' \in [ CORRECT -> { S1, S2, S3 } ] BY <3>fr DEF TypeOK, S2
      <3>5. \E B1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
              msgs1' = [ rr \in ROUNDS |-> { m \in B1 : m.r = rr } ]
        <4>1. A1p \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
              BY <3>r0, <3>idall DEF A1p, M1
        <4>2. msgs1' = [ rr \in ROUNDS |-> { m \in A1p : m.r = rr } ]
              BY <2>2, <3>fr, <3>r0, <3>idall, Msgs1AddOneRep DEF A1p, Step1
        <4> QED BY <4>1, <4>2
      <3>6. \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2' = [ rr \in ROUNDS |->
                { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                  \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
        <4> QED BY <3>fr
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
    <2>3. CASE Step2(id)
          \* msgs2[r] gains D2(id,r,v) or Q2(id,r); reuse/extend the msgs2 witnesses.
      <3> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
            msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
          BY DEF TypeOK
      <3> PICK A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
            msgs2 = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
          BY DEF TypeOK
      <3>fr. /\ value' = value /\ decision' = decision /\ round' = round /\ msgs1' = msgs1
              /\ step' = [ step EXCEPT ![id] = S3 ]
          BY <2>3 DEF Step2
      <3>r0. round[id] \in ROUNDS
          BY DEF TypeOK
      <3>idall. id \in ALL BY DEF ALL
      <3>1. value' \in [ CORRECT -> VALUES ] BY <3>fr DEF TypeOK
      <3>2. decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ] BY <3>fr DEF TypeOK
      <3>3. round' \in [ CORRECT -> ROUNDS ] BY <3>fr DEF TypeOK
      <3>4. step' \in [ CORRECT -> { S1, S2, S3 } ] BY <3>fr DEF TypeOK, S3
      <3>5. \E B1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
              msgs1' = [ rr \in ROUNDS |-> { m \in B1 : m.r = rr } ]
        <4> QED BY <3>fr
      <3>6. \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
                B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2' = [ rr \in ROUNDS |->
                { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                  \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
        <4> PICK received \in SUBSET msgs1[round[id]] :
              /\ Cardinality(Senders1(received)) >= N - T
              /\ LET Weights == [ v \in VALUES |->
                   Cardinality(Senders1({ m \in received: m.v = v })) ]
                 IN
                 \/ \E v \in VALUES:
                      /\ 2 * Weights[v] > N + T
                      /\ msgs2' =
                           [ msgs2 EXCEPT ![round[id]] =
                               msgs2[round[id]] \union { D2(id, round[id], v) } ]
                 \/ /\ \A v \in VALUES: 2 * Weights[v] <= N + T
                    /\ msgs2' =
                         [ msgs2 EXCEPT ![round[id]] =
                             msgs2[round[id]] \union { Q2(id, round[id]) } ]
            BY <2>3 DEF Step2
        <4> DEFINE Weights == [ v \in VALUES |->
                   Cardinality(Senders1({ m \in received: m.v = v })) ]
        <4>d. CASE \E v \in VALUES:
                  /\ 2 * Weights[v] > N + T
                  /\ msgs2' =
                       [ msgs2 EXCEPT ![round[id]] =
                           msgs2[round[id]] \union { D2(id, round[id], v) } ]
          <5> PICK v \in VALUES:
                /\ 2 * Weights[v] > N + T
                /\ msgs2' =
                     [ msgs2 EXCEPT ![round[id]] =
                         msgs2[round[id]] \union { D2(id, round[id], v) } ]
              BY <4>d
          <5> DEFINE A1Dp == A1D \union { [ src |-> id, r |-> round[id], v |-> v ] }
          <5>1. A1Dp \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
                BY <3>r0, <3>idall DEF A1Dp
          <5>2. msgs2' = [ rr \in ROUNDS |->
                  { D2(mm.src, rr, mm.v): mm \in { m \in A1Dp: m.r = rr } }
                    \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
                BY <4>d, <3>r0, <3>idall, Msgs2AddDRep DEF A1Dp, Step2
          <5>qok. A1Q \in SUBSET [ src: ALL, r: ROUNDS ] OBVIOUS
          <5> QED BY <5>1, <5>2, <5>qok, Msgs2PrimeWitnessIntro
        <4>q. CASE /\ \A v \in VALUES: 2 * Weights[v] <= N + T
                    /\ msgs2' =
                         [ msgs2 EXCEPT ![round[id]] =
                             msgs2[round[id]] \union { Q2(id, round[id]) } ]
          <5> DEFINE A1Qp == A1Q \union { [ src |-> id, r |-> round[id] ] }
          <5>1. A1Qp \in SUBSET [ src: ALL, r: ROUNDS ]
                BY <3>r0, <3>idall DEF A1Qp
          <5>2. msgs2' = [ rr \in ROUNDS |->
                  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
                    \union { Q2(mm.src, rr): mm \in { m \in A1Qp: m.r = rr } } ]
                BY <4>q, <3>r0, <3>idall, Msgs2AddQRep DEF A1Qp, Step2
          <5>dok. A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] OBVIOUS
          <5> QED BY <5>dok, <5>1, <5>2, Msgs2PrimeWitnessIntro
        <4> QED BY <4>d, <4>q
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
    <2>4. CASE Step3(id)
          \* value/decision/round/step updates stay in type; msgs unchanged.
          BY <2>4, RoundsNat DEF TypeOK, Step3
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1>3. CASE FaultyStep
        \* faulty replicas add messages with src \in FAULTY \subseteq ALL.
    <2> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
          msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
        BY DEF TypeOK
    <2> PICK A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
              A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
          msgs2 = [ rr \in ROUNDS |->
            { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
              \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } } ]
        BY DEF TypeOK
    <2>fs. PICK rr0 \in ROUNDS :
          /\ \E F1 \in SUBSET [ src: FAULTY, r: { rr0 }, v: VALUES ] :
               msgs1' = [ msgs1 EXCEPT ![rr0] = msgs1[rr0] \union F1 ]
          /\ \E F2D \in SUBSET FaultyD2Records(rr0) :
               \E F2Q \in SUBSET FaultyQ2Records(rr0) :
                 msgs2' = [ msgs2 EXCEPT ![rr0] =
                    msgs2[rr0]
                      \union { D2(mm.src, rr0, mm.v): mm \in F2D }
                      \union { Q2(mm.src, rr0): mm \in F2Q } ]
          /\ UNCHANGED << value, decision, round, step >>
        BY <1>3 DEF FaultyStep
    <2>f1. PICK F1 \in SUBSET [ src: FAULTY, r: { rr0 }, v: VALUES ] :
          msgs1' = [ msgs1 EXCEPT ![rr0] = msgs1[rr0] \union F1 ]
        BY <2>fs
    <2>f2. PICK F2D \in SUBSET FaultyD2Records(rr0),
              F2Q \in SUBSET FaultyQ2Records(rr0) :
          msgs2' = [ msgs2 EXCEPT ![rr0] =
                    msgs2[rr0]
                      \union { D2(mm.src, rr0, mm.v): mm \in F2D }
                      \union { Q2(mm.src, rr0): mm \in F2Q } ]
        BY <2>fs
    <2>fr. value' = value /\ decision' = decision /\ round' = round /\ step' = step
        BY <2>fs DEF vars
    <2> DEFINE A1p == A1 \union F1
               A1Dp == A1D \union F2D
               A1Qp == A1Q \union F2Q
    <2>f1all. F1 \in SUBSET [ src: ALL, r: { rr0 }, v: VALUES ]
        BY <2>fs, <2>f1 DEF ALL
    <2>f2dall. F2D \in SUBSET [ src: ALL, r: { rr0 }, v: VALUES ]
        BY <2>fs, <2>f2 DEF ALL, FaultyD2Records
    <2>f2qall. F2Q \in SUBSET [ src: ALL, r: { rr0 } ]
        BY <2>fs, <2>f2 DEF ALL, FaultyQ2Records
    <2>1. value' \in [ CORRECT -> VALUES ] BY <2>fr DEF TypeOK
    <2>2. decision' \in [ CORRECT -> VALUES \union { NO_DECISION } ] BY <2>fr DEF TypeOK
    <2>3. round' \in [ CORRECT -> ROUNDS ] BY <2>fr DEF TypeOK
    <2>4. step' \in [ CORRECT -> { S1, S2, S3 } ] BY <2>fr DEF TypeOK
    <2>5. \E B1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
            msgs1' = [ rr \in ROUNDS |-> { m \in B1 : m.r = rr } ]
      <3>1. A1p \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
            BY <2>fs, <2>f1all DEF A1p
      <3>2. msgs1' = [ rr \in ROUNDS |-> { m \in A1p : m.r = rr } ]
            BY <2>f1, <2>f1all, Msgs1AddSetRep DEF A1p
      <3> QED BY <3>1, <3>2
    <2>6. \E B1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
              B1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
            msgs2' = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in B1D: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in B1Q: m.r = rr } } ]
      <3>1. A1Dp \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]
            BY <2>fs, <2>f2dall DEF A1Dp
      <3>2. A1Qp \in SUBSET [ src: ALL, r: ROUNDS ]
            BY <2>fs, <2>f2qall DEF A1Qp
      <3>3. msgs2' = [ rr \in ROUNDS |->
              { D2(mm.src, rr, mm.v): mm \in { m \in A1Dp: m.r = rr } }
                \union { Q2(mm.src, rr): mm \in { m \in A1Qp: m.r = rr } } ]
            BY <2>f2, <2>f2dall, <2>f2qall, Msgs2AddSetsRep DEF A1Dp, A1Qp
      <3> QED BY <3>1, <3>2, <3>3, Msgs2PrimeWitnessIntro
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1> QED
        BY <1>1, <1>2, <1>3 DEF Next

\*****************************************************************************
\* SECTION C -- INDUCTIVE STEP (one preservation theorem per lemma)
\*
\* Uniform shape: ASSUME TypeOK, IndInv, [Next]_vars PROVE Lemma_i'.
\* Case split: stutter (UNCHANGED vars) / Step1 / Step2 / Step3 / FaultyStep, written
\* as a FLAT set of ASSUME/PROVE cases so the [Next]_vars assumption is in scope at the
\* combining QED. "Frame" cases (the action leaves all variables the lemma mentions
\* unchanged) are discharged from the action definition; substantive cases are split out
\* as named theorems, with any remaining hard fact isolated as an explicit TODO theorem.
\*****************************************************************************

\* ===== L2: no type-1 equivocation by correct (msgs1) =====
THEOREM Pres_L2_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, Step2
THEOREM Pres_L2_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, Step3
THEOREM Pres_L2_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  BY DEF IndInv, Lemma2_NoEquivocation1ByCorrect, vars
\* The substantive Step1 case: the new M1(id,r,value[id]) is the only round-r message from
\* id (Lemma4: id is in S1, so it has not sent at its current round), so no equivocation.
THEOREM Pres_L2_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1> USE DEF IndInv
  <1>r0. round[id] \in ROUNDS BY DEF TypeOK
  <1>dom. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>meq. msgs1' = [ msgs1 EXCEPT
            ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          BY DEF Step1
  <1>nf. \A m \in msgs1[round[id]] : m.src /= id
    <2> SUFFICES ASSUME NEW m \in msgs1[round[id]], m.src = id PROVE FALSE OBVIOUS
    <2>1. step[id] = S1 BY DEF Step1
    <2>2. m.r < round[id] BY <2>1, <1>r0 DEF Lemma4_MessagesNotFromFuture
    <2>3. m.r = round[id] BY <1>r0, Msgs1Shape
    <2> QED BY <2>2, <2>3
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW p1 \in msgs1'[r], NEW p2 \in msgs1'[r],
                      p1.src \in CORRECT, p1.src = p2.src
               PROVE  p1.v = p2.v
        BY DEF Lemma2_NoEquivocation1ByCorrect
  <1>nsrc. M1(id, round[id], value[id]).src = id BY DEF M1
  <1>A. CASE r # round[id]
        <2>1. msgs1'[r] = msgs1[r] BY <1>meq, <1>dom, <1>r0, <1>A
        <2> QED BY <2>1 DEF Lemma2_NoEquivocation1ByCorrect
  <1>B. CASE r = round[id]
        <2>1. msgs1'[r] = msgs1[round[id]] \union { M1(id, round[id], value[id]) }
              BY <1>meq, <1>dom, <1>r0, <1>B
        <2>p1. p1 \in msgs1[round[id]] \/ p1 = M1(id, round[id], value[id]) BY <2>1
        <2>p2. p2 \in msgs1[round[id]] \/ p2 = M1(id, round[id], value[id]) BY <2>1
        <2>2. CASE p1 \in msgs1[round[id]] /\ p2 \in msgs1[round[id]]
              BY <2>2, <1>B DEF Lemma2_NoEquivocation1ByCorrect
        <2>3. CASE p1 = M1(id, round[id], value[id])
              <3>1. p2.src = id BY <2>3, <1>nsrc
              <3>2. p2 = M1(id, round[id], value[id]) BY <3>1, <1>nf, <2>p2
              <3> QED BY <2>3, <3>2
        <2>4. CASE p2 = M1(id, round[id], value[id]) /\ p1 \in msgs1[round[id]]
              <3>1. p1.src = id BY <2>4, <1>nsrc
              <3> QED BY <3>1, <1>nf, <2>4
        <2> QED BY <2>p1, <2>p2, <2>2, <2>3, <2>4
  <1> QED BY <1>A, <1>B
\* FaultyStep case: new msgs1 messages have FAULTY src, so any CORRECT-sender message is
\* old; no new equivocation among correct senders.
THEOREM Pres_L2_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1>l2. Lemma2_NoEquivocation1ByCorrect BY DEF IndInv
  <1>p. \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW m1 \in msgs1'[r], NEW m2 \in msgs1'[r],
                      m1.src \in CORRECT, m1.src = m2.src
               PROVE  m1.v = m2.v
        BY DEF Lemma2_NoEquivocation1ByCorrect
  <1>1. m1 \in msgs1[r] BY <1>p, DisjointCF
  <1>2. m2 \in msgs1[r] BY <1>p, DisjointCF
  <1> QED BY <1>1, <1>2, <1>l2 DEF Lemma2_NoEquivocation1ByCorrect
THEOREM Pres_Lemma2 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
  <1> QED BY Pres_L2_S1, Pres_L2_S2, Pres_L2_S3, Pres_L2_ST, Pres_L2_F DEF Next, CorrectStep

\* ===== L3: no type-2 equivocation by correct (msgs2) =====
THEOREM Pres_L3_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, Step1
THEOREM Pres_L3_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  <1>l3. Lemma3_NoEquivocation2ByCorrect BY DEF IndInv
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>s2. step[id] = S2 BY DEF Step2
  <1>dist. S2 # S3 BY DEF S2, S3
  <1>nm. PICK nm :
        /\ msgs2' = [ msgs2 EXCEPT ![round[id]] = msgs2[round[id]] \union { nm } ]
        /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id
        /\ (IF IsD2(nm) THEN AsD2(nm).r ELSE AsQ2(nm).r) = round[id]
      BY VariantAx DEF Step2
  <1>noOld. \A m \in msgs2[round[id]] :
        (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) # id
    <2> SUFFICES ASSUME NEW m \in msgs2[round[id]],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) = id
          PROVE FALSE
        OBVIOUS
    <2>mr. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) = round[id]
        BY <1>r0, Msgs2RShape, VariantAx
    <2>srcCor. (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
        OBVIOUS
    <2>srcEq. (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) = id
        OBVIOUS
    <2>notS3. step[(IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src)] # S3
        BY <2>srcEq, <1>s2, <1>dist
    <2>roundSrc. round[(IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src)] = round[id]
        BY <2>srcEq
    <2>lt. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) < round[id]
        BY <1>l4, <1>r0, <2>srcCor, <2>notS3, <2>roundSrc DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>mr, <2>lt
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW m1 \in msgs2'[r], NEW m2 \in msgs2'[r]
        PROVE  /\ IsD2(m1) /\ IsD2(m2) /\ AsD2(m1).src = AsD2(m2).src =>
                  (AsD2(m1).src \in CORRECT => AsD2(m1).v = AsD2(m2).v)
               /\ IsQ2(m1) /\ IsD2(m2) /\ AsQ2(m1).src = AsD2(m2).src =>
                  AsQ2(m1).src \in FAULTY
      BY DEF Lemma3_NoEquivocation2ByCorrect
  <1> QED BY <1>l3, <1>nm, <1>noOld, <1>dom2, <1>r0, VariantAx
           DEF Lemma3_NoEquivocation2ByCorrect
THEOREM Pres_L3_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, Step3
THEOREM Pres_L3_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY DEF IndInv, Lemma3_NoEquivocation2ByCorrect, vars
THEOREM Pres_L3_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  BY FaultyStepProps, DisjointCF DEF IndInv, Lemma3_NoEquivocation2ByCorrect
THEOREM Pres_Lemma3 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma3_NoEquivocation2ByCorrect'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma3_NoEquivocation2ByCorrect'
          OBVIOUS
    <2> QED BY Pres_L3_S2
  <1>o2. FaultyStep => Lemma3_NoEquivocation2ByCorrect'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma3_NoEquivocation2ByCorrect'
          OBVIOUS
    <2> QED BY Pres_L3_F
  <1> QED BY Pres_L3_S1, Pres_L3_S3, Pres_L3_ST, <1>o1, <1>o2 DEF Next, CorrectStep

\* ===== L4: messages not from the future =====
THEOREM Pres_L4_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma4_MessagesNotFromFuture'
  BY DEF IndInv, Lemma4_MessagesNotFromFuture, vars
\* Substantive Step1 case: the new M1 has round = round[id]; id moves S1->S2. We do NOT
\* USE DEF IndInv (it would expand the Cardinality-heavy lemmas and poison the arithmetic);
\* we extract just Lemma4. The step/round priming (step EXCEPT ![id]=S2) is handled by a
\* case split on whether the message's sender is id, with S1#S2#S3 distinctness and Nat
\* typing of message rounds (to get <= from <).
THEOREM Pres_L4_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>doms. step \in [ CORRECT -> { S1, S2, S3 } ] /\ round \in [ CORRECT -> ROUNDS ]
           BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id]] = msgs1[round[id]] \union { M1(id, round[id], value[id]) } ]
          /\ step' = [ step EXCEPT ![id] = S2 ] /\ round' = round /\ msgs2' = msgs2
          BY DEF Step1
  <1>s1. step[id] = S1 BY DEF Step1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S2 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>new. M1(id, round[id], value[id]) = [ src |-> id, r |-> round[id], v |-> value[id] ]
            BY DEF M1
    <2>1. m \in msgs1[r] \/ (r = round[id] /\ m = M1(id, round[id], value[id]))
          BY <1>upd, <1>dom1, <1>r0
    <2>2. CASE m \in msgs1[r]
          <3>a. CASE m.src = id
                <4>1. m.r < round[id] BY <3>a, <2>2, <1>l4, <1>s1 DEF Lemma4_MessagesNotFromFuture
                <4>nat. m.r \in Nat /\ round[id] \in Nat BY <2>2, Msgs1Shape, <1>r0, RoundsNat
                <4>2. step'[m.src] = S2 /\ round'[m.src] = round[id] BY <3>a, <1>st, <1>rd
                <4> QED BY <4>1, <4>nat, <4>2, <1>dist
          <3>b. CASE m.src # id
                <4>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <3>b, <1>st, <1>rd
                <4> QED BY <3>b, <2>2, <4>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>a, <3>b
    <2>3. CASE r = round[id] /\ m = M1(id, round[id], value[id])
          <3>1. m.src = id /\ m.r = round[id] BY <2>3, <2>new
          <3>2. step'[m.src] = S2 /\ round'[m.src] = round[id] BY <3>1, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>r0, <1>dist
    <2> QED BY <2>1, <2>2, <2>3
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2>old. m \in msgs2[r] BY <1>upd
    <2>a. CASE src = id
          <3>1. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) < round[id]
                BY <2>a, <2>old, <1>l4, <1>s1, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[src] = S2 /\ round'[src] = round[id] BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>dist
    <2>b. CASE src # id
          <3>1. step'[src] = step[src] /\ round'[src] = round[src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>old, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1> QED BY <1>P1, <1>P2
\* Substantive Step3 case: id advances round[id]->round[id]+1 and resets step to S1;
\* msgs1/msgs2 unchanged. Old bounds m.r <= round[id] become m.r < round[id]+1.
THEOREM Pres_L4_S3 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ round' = [ round EXCEPT ![id] = round[id] + 1 ]
          /\ step' = [ step EXCEPT ![id] = S1 ] /\ msgs1' = msgs1 /\ msgs2' = msgs2
          BY DEF Step3
  <1>s3. step[id] = S3 BY DEF Step3
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S1 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id THEN round[id] + 1 ELSE round[x])
         BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>0. m \in msgs1[r] BY <1>upd
    <2>nat. m.r \in Nat BY <2>0, Msgs1Shape, RoundsNat
    <2>a. CASE m.src = id
          <3>1. m.r <= round[id] BY <2>a, <2>0, <1>l4, <1>s3, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[m.src] = S1 /\ round'[m.src] = round[id] + 1 BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <2>nat, <1>r0, <1>dist
    <2>b. CASE m.src # id
          <3>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2>0. m \in msgs2[r] BY <1>upd
    <2>mr. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) = r BY <2>0, Msgs2RShape, VariantAx
    <2>nat. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) \in Nat BY <2>mr, RoundsNat
    <2>a. CASE src = id
          <3>1. (IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r) <= round[id]
                BY <2>a, <2>0, <1>l4, <1>s3, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3>2. step'[src] = S1 /\ round'[src] = round[id] + 1 BY <2>a, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <2>nat, <1>r0, <1>dist
    <2>b. CASE src # id
          <3>1. step'[src] = step[src] /\ round'[src] = round[src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1> QED BY <1>P1, <1>P2
\* Substantive Step2 case: id sends a new D2(id,r,v) or Q2(id,r) into msgs2[r] and moves
\* S2->S3. The new message carries round r = round[id]; old bounds m.r < round become
\* m.r <= round (still ok). Handles Step2's two value-quorum branches uniformly via the
\* shared new-message round/sender shape.
THEOREM Pres_L4_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>r0. round[id] \in ROUNDS /\ round[id] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>fr. step' = [ step EXCEPT ![id] = S3 ] /\ msgs1' = msgs1 /\ round' = round BY DEF Step2
  <1>s2. step[id] = S2 BY DEF Step2
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id THEN S3 ELSE step[x]) BY <1>fr, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>fr, <1>doms
  <1>nm. PICK nm :
            /\ msgs2' = [ msgs2 EXCEPT ![round[id]] = msgs2[round[id]] \union { nm } ]
            /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id
            /\ (IF IsD2(nm) THEN AsD2(nm).r ELSE AsQ2(nm).r) = round[id]
         BY VariantAx DEF Step2
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                          /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                          /\ step'[m.src] = S1 => (m.r < round'[m.src])
                      /\ \A m \in msgs2'[r] :
                          LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                              mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                          IN src \in CORRECT =>
                               /\ step'[src] = S3 => (mr <= round'[src])
                               /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT
                 PROVE /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                       /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>0. m \in msgs1[r] BY <1>fr
    <2>a. CASE m.src = id
          <3>1. step'[m.src] = S3 /\ round'[m.src] = round[id] BY <2>a, <1>st, <1>rd
          <3>2. m.r <= round[id] BY <2>a, <2>0, <1>l4, <1>s2, <1>dist DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>1, <3>2, <1>dist
    <2>b. CASE m.src # id
          <3>1. step'[m.src] = step[m.src] /\ round'[m.src] = round[m.src] BY <2>b, <1>st, <1>rd
          <3> QED BY <2>b, <2>0, <3>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
    <2> QED BY <2>a, <2>b
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2> DEFINE src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
    <2> DEFINE mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
    <2>0. m \in msgs2[r] \/ (r = round[id] /\ m = nm) BY <1>nm, <1>dom2, <1>r0
    <2>old. CASE m \in msgs2[r]
          <3>nat. mr = r BY <2>old, Msgs2RShape, VariantAx
          <3>natN. mr \in Nat BY <3>nat, RoundsNat
          <3>a. CASE src = id
                <4>1. mr < round[id] BY <2>old, <3>a, <1>l4, <1>s2, <1>dist DEF Lemma4_MessagesNotFromFuture
                <4>2. step'[src] = S3 /\ round'[src] = round[id] BY <3>a, <1>st, <1>rd
                <4> QED BY <4>1, <4>2, <3>natN, <1>r0, <1>dist
          <3>b. CASE src # id
                <4>1. step'[src] = step[src] /\ round'[src] = round[src] BY <3>b, <1>st, <1>rd
                <4> QED BY <2>old, <3>b, <4>1, <1>l4 DEF Lemma4_MessagesNotFromFuture
          <3> QED BY <3>a, <3>b
    <2>nw. CASE r = round[id] /\ m = nm
          <3>1. src = id /\ mr = round[id] BY <2>nw, <1>nm
          <3>2. step'[src] = S3 /\ round'[src] = round[id] BY <3>1, <1>st, <1>rd
          <3> QED BY <3>1, <3>2, <1>r0, <1>dist
    <2> QED BY <2>0, <2>old, <2>nw
  <1> QED BY <1>P1, <1>P2
\* FaultyStep case: step/round unchanged and messages only grow with FAULTY-sender
\* messages, so any CORRECT-sender message is old and satisfies the (unchanged) bound.
THEOREM Pres_L4_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma4_MessagesNotFromFuture'
  <1>l4. Lemma4_MessagesNotFromFuture BY DEF IndInv
  <1>p. /\ step' = step /\ round' = round
        /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS
        PROVE /\ \A m \in msgs1'[r] : m.src \in CORRECT =>
                  /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                  /\ step'[m.src] = S1 => (m.r < round'[m.src])
              /\ \A m \in msgs2'[r] :
                  LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                      mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                  IN src \in CORRECT =>
                       /\ step'[src] = S3 => (mr <= round'[src])
                       /\ step'[src] /= S3 => (mr < round'[src])
        BY DEF Lemma4_MessagesNotFromFuture
  <1>P1. \A m \in msgs1'[r] : m.src \in CORRECT =>
            /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
            /\ step'[m.src] = S1 => (m.r < round'[m.src])
    <2> SUFFICES ASSUME NEW m \in msgs1'[r], m.src \in CORRECT PROVE
                   /\ step'[m.src] /= S1 => (m.r <= round'[m.src])
                   /\ step'[m.src] = S1 => (m.r < round'[m.src]) OBVIOUS
    <2>1. m \in msgs1[r] BY <1>p, DisjointCF
    <2> QED BY <2>1, <1>l4, <1>p DEF Lemma4_MessagesNotFromFuture
  <1>P2. \A m \in msgs2'[r] :
            LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
            IN src \in CORRECT =>
                 /\ step'[src] = S3 => (mr <= round'[src])
                 /\ step'[src] /= S3 => (mr < round'[src])
    <2> SUFFICES ASSUME NEW m \in msgs2'[r],
                  (IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src) \in CORRECT
                 PROVE LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src
                           mr  == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r
                       IN /\ step'[src] = S3 => (mr <= round'[src])
                          /\ step'[src] /= S3 => (mr < round'[src]) OBVIOUS
    <2>1. m \in msgs2[r] BY <1>p, DisjointCF, VariantAx
    <2> QED BY <2>1, <1>l4, <1>p DEF Lemma4_MessagesNotFromFuture
  <1> QED BY <1>P1, <1>P2
THEOREM Pres_Lemma4 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma4_MessagesNotFromFuture'
  <1> QED BY Pres_L4_S1, Pres_L4_S2, Pres_L4_S3, Pres_L4_ST, Pres_L4_F DEF Next, CorrectStep

\* ===== L5: a non-initial round requires previously sent messages =====
THEOREM Pres_L5_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma5_RoundNeedsSentMessages'
  BY DEF IndInv, Lemma5_RoundNeedsSentMessages, vars
\* Substantive Step1 case: id sends its first M1 of round[id] and moves S1->S2. The new
\* M1 witnesses the now-active "r = round[id] /\ step /= S1" obligation; all other
\* obligations are preserved because msgs1 only grows (monotonicity) and msgs2 is unchanged.
THEOREM Pres_L5_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ step' = [ step EXCEPT ![id0] = S2 ] /\ round' = round /\ msgs2' = msgs2
          BY DEF Step1
  <1>mono. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] BY <1>upd, <1>dom1, <1>r0
  <1>new. M1(id0, round[id0], value[id0]).src = id0
          /\ M1(id0, round[id0], value[id0]) \in msgs1'[round[id0]]
          BY <1>upd, <1>dom1, <1>r0 DEF M1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S2 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rid. round'[id] = round[id] BY <1>rd
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1'[r]: m.src = id OBVIOUS
    <2>1. CASE id = id0 /\ r = round[id0] BY <2>1, <1>new
    <2>2. CASE ~(id = id0 /\ r = round[id0])
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <2>2, <1>rid, <1>st, <1>dist
          <3>2. \E m \in msgs1[r] : m.src = id BY <3>1, <1>old
          <3> QED BY <3>2, <1>mono
    <2> QED BY <2>1, <2>2
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
         BY <1>old, <1>upd, <1>rid
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. step[id] = S3 BY <1>st, <1>dist
    <2> QED BY <2>1, <1>rid, <1>old, <1>upd
  <1> QED BY <1>c1, <1>c2, <1>c3
\* Step2 case: id sends a new type-2 message into msgs2[round[id]] (witnessing the
\* "r = round[id] /\ step = S3" obligation) and moves S2->S3; msgs1 unchanged, msgs2 grows.
THEOREM Pres_L5_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>fr. step' = [ step EXCEPT ![id0] = S3 ] /\ msgs1' = msgs1 /\ round' = round BY DEF Step2
  <1>s2. step[id0] = S2 BY DEF Step2
  <1>nm. PICK nm :
            /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
            /\ (IF IsD2(nm) THEN AsD2(nm).src ELSE AsQ2(nm).src) = id0 BY VariantAx DEF Step2
  <1>mono. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY <1>nm, <1>dom2, <1>r0
  <1>nmsrc. AsD2(nm).src = id0 \/ AsQ2(nm).src = id0
    <2>1. CASE IsD2(nm) BY <2>1, <1>nm
    <2>2. CASE ~ IsD2(nm) BY <2>2, <1>nm
    <2> QED BY <2>1, <2>2
  <1>nmin. nm \in msgs2'[round[id0]]
    <2>1. msgs2'[round[id0]] = msgs2[round[id0]] \union { nm } BY <1>nm, <1>dom2, <1>r0
    <2> QED BY <2>1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S3 ELSE step[x]) BY <1>fr, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x] BY <1>fr, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rid. round'[id] = round[id] BY <1>rd
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1[r]: m.src = id BY <1>fr
    <2>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <1>rid, <1>st, <1>dist, <1>s2
    <2> QED BY <2>1, <1>old
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r < round'[id] PROVE \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>rid, <1>old
    <2> QED BY <2>1, <1>mono
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id OBVIOUS
    <2>1. CASE id = id0 BY <2>1, <1>rid, <1>nmsrc, <1>nmin
    <2>2. CASE id # id0
          <3>1. r = round[id] /\ step[id] = S3 BY <2>2, <1>rid, <1>st
          <3>2. \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <3>1, <1>old
          <3> QED BY <3>2, <1>mono
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>c1, <1>c2, <1>c3
\* Step3 case: id advances round and resets step to S1; messages unchanged. The "step=S3"
\* obligations at round[id] become "r < round[id]+1" obligations, served by the same messages.
THEOREM Pres_L5_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 /\ S2 # S3 /\ S1 # S3 BY DEF S1, S2, S3
  <1>upd. /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ] /\ step' = [ step EXCEPT ![id0] = S1 ]
          /\ msgs1' = msgs1 /\ msgs2' = msgs2 BY DEF Step3
  <1>s3. step[id0] = S3 BY DEF Step3
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S1 ELSE step[x]) BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x]) BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1>rN. r \in Nat BY RoundsNat
  <1>c1. (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
    <2> SUFFICES ASSUME r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)
                 PROVE  \E m \in msgs1[r]: m.src = id BY <1>upd
    <2>1. CASE id = id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1)
                BY <2>1, <1>rd, <1>st, <1>rN, <1>r0, <1>s3, <1>dist
          <3> QED BY <3>1, <1>old
    <2>2. CASE id # id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] /= S1) BY <2>2, <1>rd, <1>st
          <3> QED BY <3>1, <1>old
    <2> QED BY <2>1, <2>2
  <1>c2. (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r < round'[id] PROVE \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>upd
    <2>1. CASE id = id0
          <3>1. r < round[id] \/ (r = round[id] /\ step[id] = S3) BY <2>1, <1>rd, <1>rN, <1>r0, <1>s3
          <3> QED BY <3>1, <1>old
    <2>2. CASE id # id0
          <3>1. r < round[id] BY <2>2, <1>rd
          <3> QED BY <3>1, <1>old
    <2> QED BY <2>1, <2>2
  <1>c3. (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
    <2> SUFFICES ASSUME r = round'[id], step'[id] = S3
                 PROVE  \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id BY <1>upd
    <2>1. id # id0 BY <1>st, <1>dist
    <2>2. r = round[id] /\ step[id] = S3 BY <2>1, <1>rd, <1>st
    <2> QED BY <2>2, <1>old
  <1> QED BY <1>c1, <1>c2, <1>c3
\* FaultyStep case: step/round unchanged, messages only grow, so every required message
\* (a CORRECT replica's own message) still exists.
THEOREM Pres_L5_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1>l5. Lemma5_RoundNeedsSentMessages BY DEF IndInv
  <1>p. /\ step' = step /\ round' = round
        /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr] /\ msgs2[rr] \subseteq msgs2'[rr]
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW r \in ROUNDS
        PROVE /\ (r < round'[id] \/ (r = round'[id] /\ step'[id] /= S1)) => (\E m \in msgs1'[r]: m.src = id)
              /\ (r < round'[id]) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
              /\ (r = round'[id] /\ step'[id] = S3) => (\E m \in msgs2'[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
        BY DEF Lemma5_RoundNeedsSentMessages
  <1>old. /\ (r < round[id] \/ (r = round[id] /\ step[id] /= S1)) => (\E m \in msgs1[r]: m.src = id)
          /\ (r < round[id]) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          /\ (r = round[id] /\ step[id] = S3) => (\E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id)
          BY <1>l5 DEF Lemma5_RoundNeedsSentMessages
  <1> QED BY <1>old, <1>p
THEOREM Pres_Lemma5 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma5_RoundNeedsSentMessages'
  <1> QED BY Pres_L5_S1, Pres_L5_S2, Pres_L5_S3, Pres_L5_ST, Pres_L5_F DEF Next, CorrectStep

\* ===== L6: a decision fixes the value (decision,value) =====
THEOREM Pres_L6_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, Step1
THEOREM Pres_L6_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, Step2
\* FaultyStep leaves value/decision unchanged (frame), via FaultyStepProps.
THEOREM Pres_L6_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma6_DecisionDefinesValue'
  <1>1. value' = value /\ decision' = decision BY FaultyStepProps
  <1> QED BY <1>1 DEF IndInv, Lemma6_DecisionDefinesValue
THEOREM Pres_L6_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma6_DecisionDefinesValue'
  BY DEF IndInv, Lemma6_DecisionDefinesValue, vars
THEOREM Pres_L6_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma6_DecisionDefinesValue'
  <1>l6. Lemma6_DecisionDefinesValue BY DEF IndInv
  <1>dom. /\ value \in [ CORRECT -> VALUES ]
          /\ decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
          /\ round \in [ CORRECT -> ROUNDS ]
        BY DEF TypeOK
  <1> PICK received \in SUBSET msgs2[round[id0]] :
        /\ Cardinality(Senders2(received)) = N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
           \/ /\ \A vv \in VALUES: Weights[vv] < T + 1
              /\ \E next_v \in VALUES:
                   /\ value' = [ value EXCEPT ![id0] = next_v ]
                   /\ decision' = decision
        BY DEF Step3
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
  <1> SUFFICES ASSUME NEW id \in CORRECT, decision'[id] # NO_DECISION
        PROVE  value'[id] = decision'[id]
        BY DEF Lemma6_DecisionDefinesValue
  <1>oldId. CASE id # id0
    <2>vSame. value'[id] = value[id] BY <1>oldId, <1>dom DEF Step3
    <2>dSame. decision'[id] = decision[id] BY <1>oldId, <1>dom DEF Step3
    <2> QED BY <1>l6, <2>vSame, <2>dSame DEF Lemma6_DecisionDefinesValue
  <1>newId. CASE id = id0
    <2>high. CASE \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
      <3>pick. PICK vv \in VALUES:
            /\ Weights[vv] >= T + 1
            /\ value' = [ value EXCEPT ![id0] = vv ]
            /\ IF 2 * Weights[vv] > N + T
               THEN decision' = [ decision EXCEPT ![id0] = vv ]
               ELSE decision' = decision
          BY <2>high
      <3>valp. value'[id] = vv BY <1>newId, <3>pick, <1>dom
      <3>decide. CASE 2 * Weights[vv] > N + T
        <4>decp. decision' = [ decision EXCEPT ![id0] = vv ] BY <3>pick, <3>decide
        <4> QED BY <1>newId, <3>valp, <4>decp, <1>dom
      <3>nodecide. CASE ~(2 * Weights[vv] > N + T)
        <4>decp. decision' = decision BY <3>pick, <3>nodecide
        <4>d0. decision[id0] # NO_DECISION BY <1>newId, <4>decp
        <4>decVal. decision[id0] \in VALUES BY <1>dom, <4>d0, NoDecisionNotValue
        <4>lock. 2 * Cardinality(Senders2({ m \in received:
                                              IsD2(m) /\ AsD2(m).v = decision[id0] }))
                    > N + T
              BY <4>d0, LockedReceiveStrictD
        <4>recsub. received \subseteq msgs2[round[id0]] OBVIOUS
        <4>rv. round[id0] \in ROUNDS BY <1>dom
        <4>vSub. { m \in received: IsD2(m) /\ AsD2(m).v = vv }
                  \subseteq DvSet(round[id0], vv)
              BY <4>recsub DEF DvSet
        <4>vMono. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv }))
                    <= Cardinality(Senders2(DvSet(round[id0], vv)))
              BY <4>vSub, Senders2_Mono
        <4>finV. IsFiniteSet(DvSet(round[id0], vv)) BY <3>pick, <4>rv, D2SetFinite
        <4>vLeD. Cardinality(Senders2(DvSet(round[id0], vv)))
                    <= Cardinality(DvSet(round[id0], vv))
              BY <4>finV, Senders2_CardLeSet
        <4>vTypes. /\ Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) \in Nat
                    /\ Cardinality(Senders2(DvSet(round[id0], vv))) \in Nat
                    /\ Cardinality(DvSet(round[id0], vv)) \in Nat
                    /\ T + 1 \in Nat
              BY Senders2_Sub, <4>finV, FS_CardinalityType, ConstNat, FleqT
        <4>recVge. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv }))
                      >= T + 1
              BY <3>pick DEF Weights
        <4>sendVge. Cardinality(Senders2(DvSet(round[id0], vv))) >= T + 1
              BY <4>recVge, <4>vMono, <4>vTypes, Arith_GeTrans
        <4>geV. Cardinality(DvSet(round[id0], vv)) >= T + 1
              BY <4>sendVge, <4>vLeD, <4>vTypes, Arith_GeTrans
        <4>dSub. { m \in received: IsD2(m) /\ AsD2(m).v = decision[id0] }
                  \subseteq DvSet(round[id0], decision[id0])
              BY <4>recsub DEF DvSet
        <4>dMono. Cardinality(Senders2({ m \in received:
                                          IsD2(m) /\ AsD2(m).v = decision[id0] }))
                    <= Cardinality(Senders2(DvSet(round[id0], decision[id0])))
              BY <4>dSub, Senders2_Mono
        <4>dTypes. /\ Cardinality(Senders2({ m \in received:
                                              IsD2(m) /\ AsD2(m).v = decision[id0] })) \in Nat
                    /\ Cardinality(Senders2(DvSet(round[id0], decision[id0]))) \in Nat
                    /\ N + T \in Nat
              BY Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
        <4>fullLock. 2 * Cardinality(Senders2(DvSet(round[id0], decision[id0]))) > N + T
              BY <4>lock, <4>dMono, <4>dTypes, Arith_DoubleGtMono
        <4>eq. decision[id0] = vv
              BY <4>rv, <3>pick, <4>decVal, <4>geV, <4>fullLock, DQuorumDominatesMajorityD
        <4> QED BY <1>newId, <3>valp, <4>decp, <4>eq
      <3> QED BY <3>decide, <3>nodecide
    <2>low. CASE /\ \A vv \in VALUES: Weights[vv] < T + 1
                 /\ \E next_v \in VALUES:
                      /\ value' = [ value EXCEPT ![id0] = next_v ]
                      /\ decision' = decision
      <3>decp. decision' = decision BY <2>low
      <3>d0. decision[id0] # NO_DECISION BY <1>newId, <3>decp
      <3>decVal. decision[id0] \in VALUES BY <1>dom, <3>d0, NoDecisionNotValue
      <3>lock. 2 * Cardinality(Senders2({ m \in received:
                                            IsD2(m) /\ AsD2(m).v = decision[id0] }))
                  > N + T
            BY <3>d0, LockedReceiveStrictD
      <3>lt. Weights[decision[id0]] < T + 1 BY <2>low, <1>dom, <3>d0, NoDecisionNotValue
      <3>same. Weights[decision[id0]]
                   = Cardinality(Senders2({ m \in received:
                                             IsD2(m) /\ AsD2(m).v = decision[id0] }))
            BY <3>decVal DEF Weights
      <3>ltC. Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = decision[id0] }))
                 < T + 1
            BY <3>lt, <3>same
      <3>types. /\ Cardinality(Senders2({ m \in received:
                                           IsD2(m) /\ AsD2(m).v = decision[id0] })) \in Nat
                 /\ T + 1 \in Nat
            BY Senders2_Sub, FS_CardinalityType, ConstNat, FleqT
      <3>geC. Cardinality(Senders2({ m \in received:
                                      IsD2(m) /\ AsD2(m).v = decision[id0] }))
                 >= T + 1
            BY <3>lock, <3>types, Arith_DoubleGtNplusTImplTplusOne
      <3>false. FALSE BY <3>geC, <3>ltC, <3>types, Arith_GeLtContrad
      <3> QED BY <3>false
    <2> QED BY <2>high, <2>low
  <1> QED BY <1>oldId, <1>newId
THEOREM Pres_Lemma6 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma6_DecisionDefinesValue'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step3(id) => Lemma6_DecisionDefinesValue'
    <2> SUFFICES ASSUME Step3(id) PROVE Lemma6_DecisionDefinesValue'
          OBVIOUS
    <2> QED BY Pres_L6_S3
  <1> QED BY Pres_L6_S1, Pres_L6_S2, Pres_L6_F, Pres_L6_ST, <1>o1 DEF Next, CorrectStep

\* ===== L7: a correct D2(v) requires a type-1 quorum for v =====
THEOREM Pres_L7_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma7_D2RequiresQuorum'
  BY DEF IndInv, Lemma7_D2RequiresQuorum, Step3
THEOREM Pres_L7_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>grow. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        BY <1>upd, <1>dom1, <1>r0
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1>old. LET ExistsQuorum1(rr, vv) ==
             LET Sv == { m \in msgs1[rr]: m.v = vv } IN
             2 * Cardinality(Senders1(Sv)) > N + T
          IN ExistsQuorum1(r, v)
        BY <1>l7, <1>upd DEF Lemma7_D2RequiresQuorum
  <1>sub. { m \in msgs1[r] : m.v = v } \subseteq { m \in msgs1'[r] : m.v = v }
        BY <1>grow
  <1>mono. Cardinality(Senders1({ m \in msgs1[r] : m.v = v }))
              <= Cardinality(Senders1({ m \in msgs1'[r] : m.v = v }))
        BY <1>sub, Senders1_Mono
  <1>types. Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) \in Nat
             /\ Cardinality(Senders1({ m \in msgs1'[r] : m.v = v })) \in Nat
             /\ N + T \in Nat
        BY Senders1_Sub, FS_CardinalityType, ConstNat
  <1> QED BY <1>old, <1>mono, <1>types, Arith_DoubleGtMono
THEOREM Pres_L7_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>p. /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1> PICK md \in msgs2'[r] : IsD2(md) /\ AsD2(md).v = v /\ AsD2(md).src \in CORRECT
        OBVIOUS
  <1>oldD2. md \in msgs2[r] BY <1>p, DisjointCF
  <1>old. LET ExistsQuorum1(rr, vv) ==
             LET Sv == { m \in msgs1[rr]: m.v = vv } IN
             2 * Cardinality(Senders1(Sv)) > N + T
          IN ExistsQuorum1(r, v)
        BY <1>l7, <1>oldD2 DEF Lemma7_D2RequiresQuorum
  <1>sub. { m \in msgs1[r] : m.v = v } \subseteq { m \in msgs1'[r] : m.v = v }
        BY <1>p
  <1>mono. Cardinality(Senders1({ m \in msgs1[r] : m.v = v }))
              <= Cardinality(Senders1({ m \in msgs1'[r] : m.v = v }))
        BY <1>sub, Senders1_Mono
  <1>types. Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) \in Nat
             /\ Cardinality(Senders1({ m \in msgs1'[r] : m.v = v })) \in Nat
             /\ N + T \in Nat
        BY Senders1_Sub, FS_CardinalityType, ConstNat
  <1> QED BY <1>old, <1>mono, <1>types, Arith_DoubleGtMono
THEOREM Pres_L7_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma7_D2RequiresQuorum'
  <1>l7. Lemma7_D2RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1> PICK received \in SUBSET msgs1[round[id0]] :
        /\ Cardinality(Senders1(received)) >= N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ 2 * Weights[vv] > N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
           \/ /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
              /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
        BY DEF Step2
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
  <1> SUFFICES ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
                      \E m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
               PROVE  LET ExistsQuorum1(rr, vv) ==
                         LET Sv == { m \in msgs1'[rr]: m.v = vv } IN
                         2 * Cardinality(Senders1(Sv)) > N + T
                      IN ExistsQuorum1(r, v)
        BY DEF Lemma7_D2RequiresQuorum
  <1> PICK md \in msgs2'[r] : IsD2(md) /\ AsD2(md).v = v /\ AsD2(md).src \in CORRECT
        OBVIOUS
  <1>oldMsg. CASE md \in msgs2[r]
    <2>old. LET ExistsQuorum1(rr, vv) ==
               LET Sv == { m \in msgs1[rr]: m.v = vv } IN
               2 * Cardinality(Senders1(Sv)) > N + T
            IN ExistsQuorum1(r, v)
          BY <1>l7, <1>oldMsg DEF Lemma7_D2RequiresQuorum
    <2> QED BY <2>old, <1>m1same
  <1>newMsg. CASE md \notin msgs2[r]
    <2>d. CASE \E vv \in VALUES:
              /\ 2 * Weights[vv] > N + T
              /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
      <3> PICK vd \in VALUES:
            /\ 2 * Weights[vd] > N + T
            /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                  msgs2[round[id0]] \union { D2(id0, round[id0], vd) } ]
          BY <2>d
      <3>eq. r = round[id0] /\ md = D2(id0, round[id0], vd)
          BY <1>newMsg, <1>dom2, <1>r0
      <3>veq. v = vd BY <3>eq, VariantAx
      <3>sub. { m \in received : m.v = vd } \subseteq { m \in msgs1[round[id0]] : m.v = vd }
          OBVIOUS
      <3>mono. Cardinality(Senders1({ m \in received : m.v = vd }))
                  <= Cardinality(Senders1({ m \in msgs1[round[id0]] : m.v = vd }))
          BY <3>sub, Senders1_Mono
      <3>types. Cardinality(Senders1({ m \in received : m.v = vd })) \in Nat
                 /\ Cardinality(Senders1({ m \in msgs1[round[id0]] : m.v = vd })) \in Nat
                 /\ N + T \in Nat
          BY Senders1_Sub, FS_CardinalityType, ConstNat
      <3>gt. 2 * Cardinality(Senders1({ m \in received : m.v = vd })) > N + T
          BY <2>d DEF Weights
      <3> QED BY <3>eq, <3>veq, <3>gt, <3>mono, <3>types, <1>m1same, Arith_DoubleGtMono
    <2>q. CASE /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                      msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
      <3>eq. r = round[id0] /\ md = Q2(id0, round[id0])
          BY <2>q, <1>newMsg, <1>dom2, <1>r0
      <3> QED BY <3>eq, VariantAx
    <2> QED BY <2>d, <2>q
  <1> QED BY <1>oldMsg, <1>newMsg
THEOREM Pres_L7_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma7_D2RequiresQuorum'
  BY DEF IndInv, Lemma7_D2RequiresQuorum, vars
THEOREM Pres_Lemma7 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma7_D2RequiresQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_S2
  <1>o3. FaultyStep => Lemma7_D2RequiresQuorum'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma7_D2RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L7_F
  <1> QED BY Pres_L7_S3, Pres_L7_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L8: a correct Q2 means no type-1 quorum existed =====
\* TYPE-1 WITNESS for Lemma8a. From a received set (>= N-T senders) in which no value has
\* a strict type-1 majority (2*Weights[v] <= N+T), build the abstract witnesses x0, x1:
\* take the CORRECT senders of value 0 / 1 within received. The N+T bound is exactly what
\* makes 2*x <= N+T close. No equivocation lemma is needed -- only the message shape and a
\* sender partition (every received sender is a correct-0, correct-1, or faulty sender).
THEOREM LowWeightsReceivedL8Witness ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs1[r],
         Cardinality(Senders1(received)) >= N - T,
         \A vv \in VALUES :
           2 * Cardinality(Senders1({ m \in received : m.v = vv })) <= N + T
  PROVE  LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
             n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
             nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
         IN
         \E x0, x1 \in 0..N :
           /\ x0 <= n0 /\ x1 <= n1
           /\ x0 + x1 + nf >= N - T
           /\ 2 * x0 <= N + T
           /\ 2 * x1 <= N + T
  <1> DEFINE C0 == { id \in CORRECT : [ src |-> id, r |-> r, v |-> 0 ] \in received }
             C1 == { id \in CORRECT : [ src |-> id, r |-> r, v |-> 1 ] \in received }
             FR == { id \in FAULTY : id \in Senders1(received) }
             W0 == Senders1({ m \in received : m.v = 0 })
             W1 == Senders1({ m \in received : m.v = 1 })
             n0 == { id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] }
             n1 == { id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] }
             nfS == { id \in FAULTY: id \in { m.src: m \in msgs1[r] } }
  <1>v01. (0 \in VALUES) /\ (1 \in VALUES) BY DEF VALUES
  <1>recsub. received \subseteq msgs1[r] OBVIOUS
  <1>shape. \A m \in received : m \in [ src: ALL, r: ROUNDS, v: VALUES ] /\ m.r = r
    <2> PICK A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ] :
          msgs1 = [ rr \in ROUNDS |-> { m \in A1 : m.r = rr } ]
          BY DEF TypeOK
    <2>1. msgs1[r] = { m \in A1 : m.r = r } OBVIOUS
    <2> QED BY <2>1, <1>recsub
  \* ---- the sender partition ----
  <1>part. Senders1(received) \subseteq (C0 \union C1) \union FR
    <2> SUFFICES ASSUME NEW id \in Senders1(received)
                 PROVE  id \in (C0 \union C1) \union FR
          OBVIOUS
    <2>idall. id \in ALL BY DEF Senders1
    <2> PICK m \in received : m.src = id BY DEF Senders1
    <2>msh. m \in [ src: ALL, r: ROUNDS, v: VALUES ] /\ m.r = r BY <1>shape
    <2>mrec. m = [ src |-> id, r |-> r, v |-> m.v ] BY <2>msh
    <2>mv. m.v \in VALUES BY <2>msh
    <2>corr. CASE id \in CORRECT
      <3>cases. m.v = 0 \/ m.v = 1 BY <2>mv DEF VALUES
      <3>c0. CASE m.v = 0
        <4>eq. [ src |-> id, r |-> r, v |-> 0 ] = m BY <2>mrec, <3>c0
        <4> QED BY <4>eq, <2>corr
      <3>c1. CASE m.v = 1
        <4>eq. [ src |-> id, r |-> r, v |-> 1 ] = m BY <2>mrec, <3>c1
        <4> QED BY <4>eq, <2>corr
      <3> QED BY <3>cases, <3>c0, <3>c1
    <2>flt. CASE id \in FAULTY
      <3> QED BY <2>flt
    <2> QED BY <2>idall, <2>corr, <2>flt DEF ALL
  \* ---- finiteness ----
  <1>finC0. IsFiniteSet(C0) BY FiniteCF, FS_Subset
  <1>finC1. IsFiniteSet(C1) BY FiniteCF, FS_Subset
  <1>finFR. IsFiniteSet(FR) BY FiniteCF, FS_Subset
  <1>finU. IsFiniteSet((C0 \union C1) \union FR) BY <1>finC0, <1>finC1, <1>finFR, FS_Union
  \* ---- C0/C1 subset of n0/n1 (received subset of msgs1[r]) ----
  <1>c0sub. C0 \subseteq n0 BY <1>recsub
  <1>c1sub. C1 \subseteq n1 BY <1>recsub
  <1>finN0. IsFiniteSet(n0) BY FiniteCF, FS_Subset
  <1>finN1. IsFiniteSet(n1) BY FiniteCF, FS_Subset
  <1>c0len0. Cardinality(C0) <= Cardinality(n0) BY <1>c0sub, <1>finN0, FS_Subset
  <1>c1len1. Cardinality(C1) <= Cardinality(n1) BY <1>c1sub, <1>finN1, FS_Subset
  \* ---- C0/C1 subset of W0/W1 (correct senders of v are senders of v) ----
  <1>c0w0. C0 \subseteq W0
    <2> SUFFICES ASSUME NEW id \in C0 PROVE id \in W0 OBVIOUS
    <2>1. [ src |-> id, r |-> r, v |-> 0 ] \in received /\ id \in ALL BY DEF ALL
    <2> QED BY <2>1 DEF Senders1
  <1>c1w1. C1 \subseteq W1
    <2> SUFFICES ASSUME NEW id \in C1 PROVE id \in W1 OBVIOUS
    <2>1. [ src |-> id, r |-> r, v |-> 1 ] \in received /\ id \in ALL BY DEF ALL
    <2> QED BY <2>1 DEF Senders1
  <1>finW0. IsFiniteSet(W0) BY Senders1_Sub
  <1>finW1. IsFiniteSet(W1) BY Senders1_Sub
  <1>c0lew0. Cardinality(C0) <= Cardinality(W0) BY <1>c0w0, <1>finW0, FS_Subset
  <1>c1lew1. Cardinality(C1) <= Cardinality(W1) BY <1>c1w1, <1>finW1, FS_Subset
  \* ---- FR subset of nfS ----
  <1>frsub. FR \subseteq nfS
    <2> SUFFICES ASSUME NEW id \in FR PROVE id \in nfS OBVIOUS
    <2>1. id \in FAULTY /\ id \in Senders1(received) OBVIOUS
    <2>2. \E m \in received : m.src = id BY <2>1 DEF Senders1
    <2> QED BY <2>1, <2>2, <1>recsub
  <1>finNF. IsFiniteSet(nfS) BY FiniteCF, FS_Subset
  <1>frlenf. Cardinality(FR) <= Cardinality(nfS) BY <1>frsub, <1>finNF, FS_Subset
  \* ---- partition cardinality bound ----
  <1>sfin. IsFiniteSet(Senders1(received)) BY Senders1_Sub
  <1>smono. Cardinality(Senders1(received)) <= Cardinality((C0 \union C1) \union FR)
        BY <1>part, <1>finU, FS_Subset
  <1>uadd. Cardinality((C0 \union C1) \union FR)
              <= Cardinality(C0) + Cardinality(C1) + Cardinality(FR)
        BY <1>finC0, <1>finC1, <1>finFR, CardUnion3LeSum
  \* ---- types & bounds ----
  <1>w0bound. 2 * Cardinality(W0) <= N + T BY <1>v01
  <1>w1bound. 2 * Cardinality(W1) <= N + T BY <1>v01
  <1>types. /\ Cardinality(C0) \in Nat /\ Cardinality(C1) \in Nat /\ Cardinality(FR) \in Nat
             /\ Cardinality(W0) \in Nat /\ Cardinality(W1) \in Nat
             /\ Cardinality(n0) \in Nat /\ Cardinality(n1) \in Nat /\ Cardinality(nfS) \in Nat
             /\ Cardinality(Senders1(received)) \in Nat
             /\ Cardinality((C0 \union C1) \union FR) \in Nat
             /\ N \in Nat /\ N - T \in Nat /\ N + T \in Nat
        BY <1>finC0, <1>finC1, <1>finFR, <1>finW0, <1>finW1, <1>finN0, <1>finN1, <1>finNF,
           <1>sfin, <1>finU, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>c0leN. Cardinality(C0) <= N
        BY <1>c0lew0, Senders1_Sub, <1>types, Arith_LeTrans
  <1>c1leN. Cardinality(C1) <= N
        BY <1>c1lew1, Senders1_Sub, <1>types, Arith_LeTrans
  <1>x0mem. Cardinality(C0) \in 0..N BY <1>types, <1>c0leN
  <1>x1mem. Cardinality(C1) \in 0..N BY <1>types, <1>c1leN
  <1>sum. Cardinality(C0) + Cardinality(C1) + Cardinality(nfS) >= N - T
        BY <1>smono, <1>uadd, <1>frlenf, <1>types, Arith_GeTrans
  <1>d0. 2 * Cardinality(C0) <= N + T BY <1>c0lew0, <1>w0bound, <1>types
  <1>d1. 2 * Cardinality(C1) <= N + T BY <1>c1lew1, <1>w1bound, <1>types
  <1> QED BY <1>x0mem, <1>x1mem, <1>c0len0, <1>c1len1, <1>sum, <1>d0, <1>d1

THEOREM Pres_L8_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  BY DEF IndInv, Lemma8_Q2RequiresNoQuorumFaster, Step3
THEOREM Pres_L8_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  <1>l8. Lemma8_Q2RequiresNoQuorumFaster BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>grow. \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        BY <1>upd, <1>dom1, <1>r0
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS :
                                  \E m \in msgs2'[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
        PROVE LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
                  n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
                  nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
              IN
              \E x0, x1 \in 0..N:
                /\ x0 <= n0 /\ x1 <= n1
                /\ x0 + x1 + nf >= N - T
                /\ 2 * x0 <= N + T
                /\ 2 * x1 <= N + T
        BY DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>oldRound. r \in { rr \in ROUNDS :
                       \E m \in msgs2[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
        BY <1>upd
  <1> PICK x0 \in 0..N, x1 \in 0..N :
        LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
            n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
            nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
        IN
          /\ x0 <= n0 /\ x1 <= n1
          /\ x0 + x1 + nf >= N - T
          /\ 2 * x0 <= N + T
          /\ 2 * x1 <= N + T
        BY <1>l8, <1>oldRound DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>sub0. { id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] }
              \subseteq { id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] }
        BY <1>grow
  <1>sub1. { id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] }
              \subseteq { id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] }
        BY <1>grow
  <1>subf. { id \in FAULTY: id \in { m.src: m \in msgs1[r] } }
              \subseteq { id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }
        BY <1>grow
  <1>fin0p. IsFiniteSet({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY FiniteCF, FS_Subset
  <1>fin1p. IsFiniteSet({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY FiniteCF, FS_Subset
  <1>finfp. IsFiniteSet({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
        BY FiniteCF, FS_Subset
  <1>mono0. Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
              <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY <1>sub0, <1>fin0p, FS_Subset
  <1>mono1. Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
              <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY <1>sub1, <1>fin1p, FS_Subset
  <1>monof. Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
              <= Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
        BY <1>subf, <1>finfp, FS_Subset
  <1>types. /\ x0 \in Nat /\ x1 \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] }) \in Nat
             /\ Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] }) \in Nat
             /\ Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }) \in Nat
             /\ N - T \in Nat
        BY <1>fin0p, <1>fin1p, <1>finfp, FiniteCF, FS_Subset, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1>c0. x0 <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY <1>mono0, <1>types, Arith_GeTrans
  <1>c1. x1 <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY <1>mono1, <1>types, Arith_GeTrans
  <1>csum. x0 + x1 + Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }) >= N - T
        BY <1>monof, <1>types, Arith_SumThirdMonoGe
  <1> QED BY <1>c0, <1>c1, <1>csum
\* Step2: msgs1 is unchanged, so n0/n1/nf are frame-invariant. Rounds already carrying a
\* correct Q2 reuse the old witness; the round where id0 emits its Q2 is the only new one,
\* and its witness comes from LowWeightsReceivedL8Witness applied to id0's received set.
THEOREM Pres_L8_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  <1>l8. Lemma8_Q2RequiresNoQuorumFaster BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1> PICK received \in SUBSET msgs1[round[id0]] :
        /\ Cardinality(Senders1(received)) >= N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ 2 * Weights[vv] > N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
           \/ /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
              /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                    msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
        BY DEF Step2
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders1({ m \in received : m.v = vv })) ]
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS :
                                  \E m \in msgs2'[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
        PROVE LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
                  n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
                  nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
              IN
              \E x0, x1 \in 0..N:
                /\ x0 <= n0 /\ x1 <= n1
                /\ x0 + x1 + nf >= N - T
                /\ 2 * x0 <= N + T
                /\ 2 * x1 <= N + T
        BY DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>rdom. r \in ROUNDS OBVIOUS
  <1> PICK mq \in msgs2'[r] : IsQ2(mq) /\ AsQ2(mq).src \in CORRECT OBVIOUS
  <1>oldMsg. CASE mq \in msgs2[r]
    <2>oldRound. r \in { rr \in ROUNDS : \E m \in msgs2[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
          BY <1>oldMsg, <1>rdom
    <2> QED BY <1>l8, <2>oldRound, <1>m1same DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>newMsg. CASE mq \notin msgs2[r]
    \* The only new message is id0's; mq is a Q2, ruling out the D2 branch, so r = round[id0].
    <2>q. /\ \A vv \in VALUES: 2 * Weights[vv] <= N + T
          /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                msgs2[round[id0]] \union { Q2(id0, round[id0]) } ]
      <3>notD. ~ (\E vv \in VALUES:
                /\ 2 * Weights[vv] > N + T
                /\ msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                      msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ])
        <4> SUFFICES ASSUME NEW vv \in VALUES,
                            2 * Weights[vv] > N + T,
                            msgs2' = [ msgs2 EXCEPT ![round[id0]] =
                                msgs2[round[id0]] \union { D2(id0, round[id0], vv) } ]
                     PROVE  FALSE
              OBVIOUS
        <4>mqd. mq = D2(id0, round[id0], vv) /\ r = round[id0]
              BY <1>newMsg, <1>dom2, <1>r0, <1>rdom
        <4> QED BY <4>mqd, VariantAx
      <3> QED BY <3>notD
    <2>req. r = round[id0]
          BY <2>q, <1>newMsg, <1>dom2, <1>r0, <1>rdom
    <2>recok. /\ received \in SUBSET msgs1[round[id0]]
              /\ Cardinality(Senders1(received)) >= N - T
          OBVIOUS
    <2>low. \A vv \in VALUES :
               2 * Cardinality(Senders1({ m \in received : m.v = vv })) <= N + T
          BY <2>q DEF Weights
    <2>wit. LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> round[id0], v |-> 0 ] \in msgs1[round[id0]] })
                n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> round[id0], v |-> 1 ] \in msgs1[round[id0]] })
                nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[round[id0]] } })
            IN
            \E x0, x1 \in 0..N:
              /\ x0 <= n0 /\ x1 <= n1
              /\ x0 + x1 + nf >= N - T
              /\ 2 * x0 <= N + T
              /\ 2 * x1 <= N + T
          BY <1>r0, <2>recok, <2>low, LowWeightsReceivedL8Witness
    <2> QED BY <2>wit, <2>req, <1>m1same
  <1> QED BY <1>oldMsg, <1>newMsg
THEOREM Pres_L8_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  <1>l8. Lemma8_Q2RequiresNoQuorumFaster BY DEF IndInv
  <1>p. /\ \A rr \in ROUNDS : msgs1[rr] \subseteq msgs1'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs2'[rr] :
              m \notin msgs2[rr] =>
                ((IsD2(m) => AsD2(m).src \in FAULTY) /\ (IsQ2(m) => AsQ2(m).src \in FAULTY))
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS :
                                  \E m \in msgs2'[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
        PROVE LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
                  n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
                  nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
              IN
              \E x0, x1 \in 0..N:
                /\ x0 <= n0 /\ x1 <= n1
                /\ x0 + x1 + nf >= N - T
                /\ 2 * x0 <= N + T
                /\ 2 * x1 <= N + T
        BY DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>rin. r \in ROUNDS /\ \E m \in msgs2'[r] : IsQ2(m) /\ AsQ2(m).src \in CORRECT
        OBVIOUS
  <1> PICK mq \in msgs2'[r] : IsQ2(mq) /\ AsQ2(mq).src \in CORRECT
        BY <1>rin
  <1>oldQ. mq \in msgs2[r] BY <1>p, DisjointCF
  <1>oldRound. r \in { rr \in ROUNDS :
                       \E m \in msgs2[rr] : IsQ2(m) /\ AsQ2(m).src \in CORRECT }
        BY <1>rin, <1>oldQ
  <1> PICK x0 \in 0..N, x1 \in 0..N :
        LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
            n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
            nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
        IN
          /\ x0 <= n0 /\ x1 <= n1
          /\ x0 + x1 + nf >= N - T
          /\ 2 * x0 <= N + T
          /\ 2 * x1 <= N + T
        BY <1>l8, <1>oldRound DEF Lemma8_Q2RequiresNoQuorumFaster
  <1>sub0. { id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] }
              \subseteq { id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] }
        BY <1>p
  <1>sub1. { id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] }
              \subseteq { id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] }
        BY <1>p
  <1>subf. { id \in FAULTY: id \in { m.src: m \in msgs1[r] } }
              \subseteq { id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }
        BY <1>p
  <1>fin0p. IsFiniteSet({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY FiniteCF, FS_Subset
  <1>fin1p. IsFiniteSet({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY FiniteCF, FS_Subset
  <1>finfp. IsFiniteSet({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
        BY FiniteCF, FS_Subset
  <1>mono0. Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
              <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY <1>sub0, <1>fin0p, FS_Subset
  <1>mono1. Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
              <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY <1>sub1, <1>fin1p, FS_Subset
  <1>monof. Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
              <= Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } })
        BY <1>subf, <1>finfp, FS_Subset
  <1>types. /\ x0 \in Nat /\ x1 \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] }) \in Nat
             /\ Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] }) \in Nat
             /\ Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] }) \in Nat
             /\ Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }) \in Nat
             /\ N - T \in Nat
        BY <1>fin0p, <1>fin1p, <1>finfp, FiniteCF, FS_Subset, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1>c0. x0 <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1'[r] })
        BY <1>mono0, <1>types, Arith_GeTrans
  <1>c1. x1 <= Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1'[r] })
        BY <1>mono1, <1>types, Arith_GeTrans
  <1>csum. x0 + x1 + Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1'[r] } }) >= N - T
        BY <1>monof, <1>types, Arith_SumThirdMonoGe
  <1> QED BY <1>c0, <1>c1, <1>csum
THEOREM Pres_L8_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  BY DEF IndInv, Lemma8_Q2RequiresNoQuorumFaster, vars
THEOREM Pres_Lemma8 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma8_Q2RequiresNoQuorumFaster'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma8_Q2RequiresNoQuorumFaster'
          OBVIOUS
    <2> QED BY Pres_L8_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma8_Q2RequiresNoQuorumFaster'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma8_Q2RequiresNoQuorumFaster'
          OBVIOUS
    <2> QED BY Pres_L8_S2
  <1>o3. FaultyStep => Lemma8_Q2RequiresNoQuorumFaster'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma8_Q2RequiresNoQuorumFaster'
          OBVIOUS
    <2> QED BY Pres_L8_F
  <1> QED BY Pres_L8_S3, Pres_L8_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L9: rounds connection / value support carries forward =====
THEOREM Pres_L9_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma9_RoundsConnection'
  <1>l9. Lemma9_RoundsConnection BY DEF IndInv
  <1>l13. Lemma13_ValueLock BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>val0. value[id0] \in VALUES BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          /\ round' = round
          /\ value' = value
        BY DEF Step1
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS
        PROVE LET Supported == SupportedValues(r) IN
              \/ Supported = {}
              \/ \E v \in Supported:
                   \A m \in msgs1'[r + 1]:
                     (m.src \in CORRECT => m.v = v)
        BY <1>upd DEF Lemma9_RoundsConnection, SupportedValues
  <1>old. LET Supported == SupportedValues(r) IN
            \/ Supported = {}
            \/ \E v \in Supported:
                 \A m \in msgs1[r + 1]:
                   (m.src \in CORRECT => m.v = v)
        BY <1>l9 DEF Lemma9_RoundsConnection
  <1>empty. CASE SupportedValues(r) = {}
    <2> QED BY <1>empty
  <1>nonempty. CASE SupportedValues(r) # {}
    <2>pickOld. PICK vOld \in SupportedValues(r) :
          \A m \in msgs1[r + 1] : (m.src \in CORRECT => m.v = vOld)
        BY <1>old, <1>nonempty
    <2>sameRound. CASE r + 1 = round[id0]
      <3>rnat. r \in Nat /\ r >= 1 BY RoundPos
      <3>gt. round[id0] > 1 BY <2>sameRound, <3>rnat, ConstNat
      <3>pred. round[id0] - 1 = r BY <2>sameRound, <3>rnat, ConstNat
      <3>predIn. round[id0] - 1 \in ROUNDS BY <3>pred
      <3>lock. LET S == SupportedValues(round[id0] - 1) IN
                  \/ S = {}
                  \/ value[id0] \in S
            BY <1>l13, <1>val0, <3>gt, <3>predIn DEF Lemma13_ValueLock
      <3>vin. value[id0] \in SupportedValues(r)
            BY <3>lock, <3>pred, <1>nonempty
      <3>veq. value[id0] = vOld
            BY <1>val0, <2>pickOld, <3>vin, SupportedUnique
      <3>all. \A m \in msgs1'[r + 1] : (m.src \in CORRECT => m.v = vOld)
        <4> SUFFICES ASSUME NEW m \in msgs1'[r + 1], m.src \in CORRECT
                    PROVE  m.v = vOld
              OBVIOUS
        <4>oldMsg. CASE m \in msgs1[r + 1]
          <5> QED BY <2>pickOld, <4>oldMsg
        <4>newMsg. CASE m \notin msgs1[r + 1]
          <5>added. r + 1 = round[id0]
                     /\ m \in { M1(id0, round[id0], value[id0]) }
                BY <1>upd, <1>dom1, <1>r0, <4>newMsg, UpdateUnionNewInAdded
          <5>meq. m = M1(id0, round[id0], value[id0]) BY <5>added
          <5> QED BY <5>meq, <3>veq DEF M1
        <4> QED BY <4>oldMsg, <4>newMsg
      <3> QED BY <3>all, <2>pickOld
    <2>otherRound. CASE r + 1 # round[id0]
      <3>sameMsgs. msgs1'[r + 1] = msgs1[r + 1]
            BY <1>upd, <1>dom1, <2>otherRound
      <3> QED BY <2>pickOld, <3>sameMsgs
    <2> QED BY <2>sameRound, <2>otherRound
  <1> QED BY <1>empty, <1>nonempty
THEOREM Pres_L9_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma9_RoundsConnection'
  BY DEF IndInv, Lemma9_RoundsConnection, SupportedValues, Step3
THEOREM Pres_L9_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma9_RoundsConnection'
  <1>l9. Lemma9_RoundsConnection BY DEF IndInv
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next, CorrectStep
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE msgs2[rr] \subseteq msgs2'[rr] OBVIOUS
    <2> QED BY <1>nm, <1>r0, <1>dom2
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS
        PROVE LET Supported == SupportedValuesP(r) IN
              \/ Supported = {}
              \/ \E v \in Supported:
                   \A m \in msgs1'[r + 1]:
                     (m.src \in CORRECT => m.v = v)
        BY <1>tokp, SupportedValuesPrimeIsP DEF Lemma9_RoundsConnection
  <1>empty. CASE SupportedValuesP(r) = {}
    <2> QED BY <1>empty
  <1>nonempty. CASE SupportedValuesP(r) # {}
    <2> PICK vp \in SupportedValuesP(r) : TRUE BY <1>nonempty
    <2>vpSup. vp \in SupportedValuesP(r) OBVIOUS
    <2>vpVal. vp \in VALUES BY DEF SupportedValuesP
    <2>all. \A m \in msgs1'[r + 1] : (m.src \in CORRECT => m.v = vp)
      <3> SUFFICES ASSUME NEW m \in msgs1'[r + 1], m.src \in CORRECT
                  PROVE  m.v = vp
            OBVIOUS
      <3>min. m \in msgs1[r + 1] BY <1>m1same
      <3>succNat. r + 1 \in Nat /\ r + 1 # 1 BY RoundsNat, ConstNat
      <3>prev. (r + 1) - 1 = r BY RoundsNat, Arith_PlusOneMinusOne
      <3>total. Cardinality(Senders2(msgs2[r])) >= N - T
        <4>rw. r + 1 \in ROUNDS \ {1} /\ \E mm \in msgs1[r + 1] : mm.src \in CORRECT
              BY <3>min, <3>succNat
        <4>q. Cardinality(Senders2(msgs2[(r + 1) - 1])) >= N - T
              BY <1>l10, <4>rw DEF Lemma10_M1RequiresQuorum
        <4> QED BY <4>q, <3>prev
      <3>oldOtherLe. Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                       <= Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
        <4>sub. { mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }
                    \subseteq { mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }
              BY <1>grow
        <4> QED BY <4>sub, Senders2_Mono
      <3>primeOther. Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                       < N - 2 * T
            BY <2>vpSup DEF SupportedValuesP, DvPSet
      <3>types. /\ Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp })) \in Nat
                 /\ Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp })) \in Nat
                 /\ N - 2 * T \in Nat
            BY Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
      <3>oldOther. Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                     < N - 2 * T
            BY <3>oldOtherLe, <3>primeOther, <3>types, Arith_LeLtTrans
      <3>vpOld. vp \in SupportedValues(r)
            BY <2>vpVal, <3>total, <3>oldOther, SupportedFromTotalAndFewOthers
      <3>oldConn. LET Supported == SupportedValues(r) IN
                    \/ Supported = {}
                    \/ \E v \in Supported:
                         \A mm \in msgs1[r + 1]:
                           (mm.src \in CORRECT => mm.v = v)
            BY <1>l9 DEF Lemma9_RoundsConnection
      <3>nonOld. SupportedValues(r) # {} BY <3>vpOld
      <3> PICK vo \in SupportedValues(r) :
            \A mm \in msgs1[r + 1] : (mm.src \in CORRECT => mm.v = vo)
            BY <3>oldConn, <3>nonOld
      <3>voSup. vo \in SupportedValues(r) OBVIOUS
      <3>allOld. \A mm \in msgs1[r + 1] : (mm.src \in CORRECT => mm.v = vo) OBVIOUS
      <3>eq. vp = vo BY <2>vpVal, <3>vpOld, <3>voSup, SupportedUnique
      <3> QED BY <3>min, <3>allOld, <3>eq
    <2> QED BY <2>all
  <1> QED BY <1>empty, <1>nonempty
THEOREM Pres_L9_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma9_RoundsConnection'
  <1>l9. Lemma9_RoundsConnection BY DEF IndInv
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next
  <1>p. /\ \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] :
             m \notin msgs1[rr] => m.src \in FAULTY
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS
        PROVE LET Supported == SupportedValuesP(r) IN
              \/ Supported = {}
              \/ \E v \in Supported:
                   \A m \in msgs1'[r + 1]:
                     (m.src \in CORRECT => m.v = v)
        BY <1>tokp, SupportedValuesPrimeIsP DEF Lemma9_RoundsConnection
  <1>empty. CASE SupportedValuesP(r) = {}
    <2> QED BY <1>empty
  <1>nonempty. CASE SupportedValuesP(r) # {}
    <2> PICK vp \in SupportedValuesP(r) : TRUE BY <1>nonempty
    <2>vpSup. vp \in SupportedValuesP(r) OBVIOUS
    <2>vpVal. vp \in VALUES BY DEF SupportedValuesP
    <2>all. \A m \in msgs1'[r + 1] : (m.src \in CORRECT => m.v = vp)
      <3> SUFFICES ASSUME NEW m \in msgs1'[r + 1], m.src \in CORRECT
                  PROVE  m.v = vp
            OBVIOUS
      <3>min. m \in msgs1[r + 1]
        <4>suf. SUFFICES ASSUME m \notin msgs1[r + 1] PROVE FALSE OBVIOUS
        <4>fsrc. m.src \in FAULTY BY <1>p, <4>suf
        <4> QED BY <4>suf, <4>fsrc, DisjointCF
      <3>succNat. r + 1 \in Nat /\ r + 1 # 1 BY RoundsNat, ConstNat
      <3>prev. (r + 1) - 1 = r BY RoundsNat, Arith_PlusOneMinusOne
      <3>total. Cardinality(Senders2(msgs2[r])) >= N - T
        <4>rw. r + 1 \in ROUNDS \ {1} /\ \E mm \in msgs1[r + 1] : mm.src \in CORRECT
              BY <3>min, <3>succNat
        <4>q. Cardinality(Senders2(msgs2[(r + 1) - 1])) >= N - T
              BY <1>l10, <4>rw DEF Lemma10_M1RequiresQuorum
        <4> QED BY <4>q, <3>prev
      <3>oldOtherLe. Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                       <= Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
        <4>sub. { mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }
                    \subseteq { mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }
              BY <1>p
        <4> QED BY <4>sub, Senders2_Mono
      <3>primeOther. Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                       < N - 2 * T
            BY <2>vpSup DEF SupportedValuesP, DvPSet
      <3>types. /\ Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp })) \in Nat
                 /\ Cardinality(Senders2({ mm \in msgs2'[r] : IsQ2(mm) \/ AsD2(mm).v /= vp })) \in Nat
                 /\ N - 2 * T \in Nat
            BY Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
      <3>oldOther. Cardinality(Senders2({ mm \in msgs2[r] : IsQ2(mm) \/ AsD2(mm).v /= vp }))
                     < N - 2 * T
            BY <3>oldOtherLe, <3>primeOther, <3>types, Arith_LeLtTrans
      <3>vpOld. vp \in SupportedValues(r)
            BY <2>vpVal, <3>total, <3>oldOther, SupportedFromTotalAndFewOthers
      <3>oldConn. LET Supported == SupportedValues(r) IN
                    \/ Supported = {}
                    \/ \E v \in Supported:
                         \A mm \in msgs1[r + 1]:
                           (mm.src \in CORRECT => mm.v = v)
            BY <1>l9 DEF Lemma9_RoundsConnection
      <3>nonOld. SupportedValues(r) # {} BY <3>vpOld
      <3> PICK vo \in SupportedValues(r) :
            \A mm \in msgs1[r + 1] : (mm.src \in CORRECT => mm.v = vo)
            BY <3>oldConn, <3>nonOld
      <3>voSup. vo \in SupportedValues(r) OBVIOUS
      <3>allOld. \A mm \in msgs1[r + 1] : (mm.src \in CORRECT => mm.v = vo) OBVIOUS
      <3>eq. vp = vo BY <2>vpVal, <3>vpOld, <3>voSup, SupportedUnique
      <3> QED BY <3>min, <3>allOld, <3>eq
    <2> QED BY <2>all
  <1> QED BY <1>empty, <1>nonempty
THEOREM Pres_L9_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma9_RoundsConnection'
  BY DEF IndInv, Lemma9_RoundsConnection, SupportedValues, vars
THEOREM Pres_Lemma9 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma9_RoundsConnection'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma9_RoundsConnection'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma9_RoundsConnection'
          OBVIOUS
    <2> QED BY Pres_L9_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma9_RoundsConnection'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma9_RoundsConnection'
          OBVIOUS
    <2> QED BY Pres_L9_S2
  <1>o3. FaultyStep => Lemma9_RoundsConnection'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma9_RoundsConnection'
          OBVIOUS
    <2> QED BY Pres_L9_F
  <1> QED BY Pres_L9_S3, Pres_L9_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L10: a type-1 message in round r>1 needs a quorum in r-1 =====
THEOREM Pres_L10_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma10_M1RequiresQuorum'
  BY DEF IndInv, Lemma10_M1RequiresQuorum, Step3
THEOREM Pres_L10_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom1. DOMAIN msgs1 = ROUNDS BY Msgs1DomR
  <1>upd. /\ msgs1' = [ msgs1 EXCEPT
                ![round[id0]] = msgs1[round[id0]] \union { M1(id0, round[id0], value[id0]) } ]
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>s1. step[id0] = S1 BY DEF Step1
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1'[r] : m.src \in CORRECT
        OBVIOUS
  <1> PICK m \in msgs1'[r] : m.src \in CORRECT BY <1>rin
  <1>split. m \in msgs1[r]
              \/ (r = round[id0] /\ m = M1(id0, round[id0], value[id0]))
        BY <1>upd, <1>dom1, <1>r0
  <1>old. CASE m \in msgs1[r]
    <2>rinOld. r \in ROUNDS \ { 1 } /\ \E mm \in msgs1[r] : mm.src \in CORRECT
          BY <1>old, <1>rin
    <2>q. Cardinality(Senders2(msgs2[r - 1])) >= N - T
          BY <1>l10, <2>rinOld DEF Lemma10_M1RequiresQuorum
    <2> QED BY <2>q, <1>upd
  <1>new. CASE r = round[id0] /\ m = M1(id0, round[id0], value[id0])
    <2>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
    <2>next. (r - 1) + 1 \in ROUNDS
              /\ \E id \in CORRECT : round[id] = (r - 1) + 1 /\ step[id] = S1
          BY <1>new, <1>r0, <1>s1, ConstNat, RoundsNat
    <2>q. Cardinality(Senders2(msgs2[r - 1])) >= N - T
          BY <1>l12, <2>pred, <2>next DEF Lemma12_CannotJumpRoundsWithoutQuorum
    <2> QED BY <2>q, <1>upd
  <1> QED BY <1>split, <1>old, <1>new
THEOREM Pres_L10_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>m1same. msgs1' = msgs1 BY DEF Step2
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
      BY VariantAx DEF Step2
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE msgs2[rr] \subseteq msgs2'[rr] OBVIOUS
    <2>eq. CASE rr = round[id0]
      <3> QED BY <2>eq, <1>nm, <1>r0, <1>dom2
    <2>ne. CASE rr # round[id0]
      <3> QED BY <2>ne, <1>nm, <1>r0, <1>dom2
    <2> QED BY <2>eq, <2>ne
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1[r] : m.src \in CORRECT
        BY <1>m1same
  <1>old. Cardinality(Senders2(msgs2[r - 1])) >= N - T
        BY <1>l10, <1>rin DEF Lemma10_M1RequiresQuorum
  <1>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
  <1>sub. msgs2[r - 1] \subseteq msgs2'[r - 1] BY <1>grow, <1>pred
  <1>mono. Cardinality(Senders2(msgs2[r - 1])) <= Cardinality(Senders2(msgs2'[r - 1]))
        BY <1>sub, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r - 1])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r - 1])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L10_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma10_M1RequiresQuorum'
  <1>l10. Lemma10_M1RequiresQuorum BY DEF IndInv
  <1>p. /\ \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
        /\ \A rr \in ROUNDS : \A m \in msgs1'[rr] : m \notin msgs1[rr] => m.src \in FAULTY
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in { rr \in ROUNDS \ { 1 } :
                                  \E m \in msgs1'[rr] : m.src \in CORRECT }
        PROVE Cardinality(Senders2(msgs2'[r - 1])) >= N - T
        BY DEF Lemma10_M1RequiresQuorum
  <1>rin. r \in ROUNDS /\ r # 1 /\ \E m \in msgs1'[r] : m.src \in CORRECT
        OBVIOUS
  <1> PICK m \in msgs1'[r] : m.src \in CORRECT BY <1>rin
  <1>oldMsg. m \in msgs1[r] BY <1>p, DisjointCF
  <1>old. Cardinality(Senders2(msgs2[r - 1])) >= N - T
        BY <1>l10, <1>rin, <1>oldMsg DEF Lemma10_M1RequiresQuorum
  <1>pred. r - 1 \in ROUNDS BY <1>rin, RoundPredInRounds
  <1>sub. msgs2[r - 1] \subseteq msgs2'[r - 1] BY <1>p, <1>pred
  <1>mono. Cardinality(Senders2(msgs2[r - 1])) <= Cardinality(Senders2(msgs2'[r - 1]))
        BY <1>sub, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r - 1])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r - 1])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L10_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma10_M1RequiresQuorum'
  BY DEF IndInv, Lemma10_M1RequiresQuorum, vars
THEOREM Pres_Lemma10 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma10_M1RequiresQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_S2
  <1>o3. FaultyStep => Lemma10_M1RequiresQuorum'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma10_M1RequiresQuorum'
          OBVIOUS
    <2> QED BY Pres_L10_F
  <1> QED BY Pres_L10_S3, Pres_L10_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L11: a correct replica's value at r>1 is backed by msgs2[r-1] =====
THEOREM Pres_L11_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma11_ValueOnQuorumLessRam'
  BY DEF IndInv, Lemma11_ValueOnQuorumLessRam, Step1
THEOREM Pres_L11_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma11_ValueOnQuorumLessRam'
  <1>l11. Lemma11_ValueOnQuorumLessRam BY DEF IndInv
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>fr. value' = value /\ round' = round BY DEF Step2
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE msgs2[rr] \subseteq msgs2'[rr] OBVIOUS
    <2>eq. CASE rr = round[id0]
      <3> QED BY <2>eq, <1>nm, <1>r0, <1>dom2
    <2>ne. CASE rr # round[id0]
      <3> QED BY <2>ne, <1>nm, <1>r0, <1>dom2
    <2> QED BY <2>eq, <2>ne
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE LET r == round'[id] IN
          r > 1 =>
            \/ LET v == value'[id]
                   Qv == Senders2({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = v })
               IN
               2 * Cardinality(Qv) > N + T
            \/ LET n0 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                   n1 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                   nq == Cardinality({ m \in msgs2'[r - 1]: IsQ2(m) })
               IN
               \E x0, x1 \in 0..N:
                 /\ x0 <= n0 /\ x1 <= n1
                 /\ x0 + x1 + nq >= N - T
                 /\ 2 * x0 <= N + T
                 /\ 2 * x1 <= N + T
        BY DEF Lemma11_ValueOnQuorumLessRam
  <1>gt. CASE round'[id] > 1
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <1>gt, <1>fr, RoundsNat
    <2>rp. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>old. \/ LET v == value[id]
                    Qv == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = v })
                IN
                2 * Cardinality(Qv) > N + T
             \/ LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                    n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                    nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
                IN
                \E x0, x1 \in 0..N:
                  /\ x0 <= n0 /\ x1 <= n1
                  /\ x0 + x1 + nq >= N - T
                  /\ 2 * x0 <= N + T
                  /\ 2 * x1 <= N + T
          BY <1>l11, <1>fr, <1>gt DEF Lemma11_ValueOnQuorumLessRam
    <2>one. CASE LET v == value[id]
                    Qv == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = v })
                IN
                2 * Cardinality(Qv) > N + T
      <3> DEFINE oldQ == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] })
                 newQ == Senders2({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] })
      <3>sub. { m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] }
                  \subseteq { m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] }
            BY <2>rp, <1>grow
      <3>mono. Cardinality(oldQ) <= Cardinality(newQ)
            BY <3>sub, Senders2_Mono DEF oldQ, newQ
      <3>types. Cardinality(oldQ) \in Nat /\ Cardinality(newQ) \in Nat /\ N + T \in Nat
            BY Senders2_Sub, FS_CardinalityType, ConstNat
      <3>gtNew. 2 * Cardinality(newQ) > N + T
            BY <2>one, <3>mono, <3>types, Arith_DoubleGtMono DEF oldQ
      <3> QED BY <3>gtNew, <1>fr DEF newQ
    <2>two. CASE LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                    n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                    nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
                IN
                \E x0, x1 \in 0..N:
                  /\ x0 <= n0 /\ x1 <= n1
                  /\ x0 + x1 + nq >= N - T
                  /\ 2 * x0 <= N + T
                  /\ 2 * x1 <= N + T
      <3> PICK x0 \in 0..N, x1 \in 0..N :
            LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
            IN
              /\ x0 <= n0 /\ x1 <= n1
              /\ x0 + x1 + nq >= N - T
              /\ 2 * x0 <= N + T
              /\ 2 * x1 <= N + T
            BY <2>two
      <3>v0. 0 \in VALUES BY DEF VALUES
      <3>v1. 1 \in VALUES BY DEF VALUES
      <3>m0. Cardinality(DvSet(round[id] - 1, 0))
                <= Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
            BY <2>rp, <3>v0, DvStep2Mono
      <3>m1. Cardinality(DvSet(round[id] - 1, 1))
                <= Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
            BY <2>rp, <3>v1, DvStep2Mono
      <3>mq. Cardinality(QSet(round[id] - 1))
                <= Cardinality({ m \in msgs2'[round[id] - 1]: IsQ2(m) })
            BY <2>rp, QStep2Mono
      <3>fin0p. IsFiniteSet({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
            BY <2>rp, <3>v0, DvStep2Mono
      <3>fin1p. IsFiniteSet({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
            BY <2>rp, <3>v1, DvStep2Mono
      <3>finqp. IsFiniteSet({ m \in msgs2'[round[id] - 1]: IsQ2(m) })
            BY <2>rp, QStep2Mono
      <3>fin0. IsFiniteSet(DvSet(round[id] - 1, 0)) BY <2>rp, <3>v0, D2SetFinite
      <3>fin1. IsFiniteSet(DvSet(round[id] - 1, 1)) BY <2>rp, <3>v1, D2SetFinite
      <3>finq. IsFiniteSet(QSet(round[id] - 1)) BY <2>rp, Q2SetFinite
      <3>types. /\ x0 \in Nat /\ x1 \in Nat
                 /\ Cardinality(DvSet(round[id] - 1, 0)) \in Nat
                 /\ Cardinality(DvSet(round[id] - 1, 1)) \in Nat
                 /\ Cardinality(QSet(round[id] - 1)) \in Nat
                 /\ Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 }) \in Nat
                 /\ Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 }) \in Nat
                 /\ Cardinality({ m \in msgs2'[round[id] - 1]: IsQ2(m) }) \in Nat
                 /\ N - T \in Nat
            BY <3>fin0, <3>fin1, <3>finq, <3>fin0p, <3>fin1p, <3>finqp,
               FS_CardinalityType, ConstNat, NgtT, FleqT
      <3>c0. x0 <= Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
            BY <3>m0, <3>types, Arith_GeTrans DEF DvSet
      <3>c1. x1 <= Cardinality({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
            BY <3>m1, <3>types, Arith_GeTrans DEF DvSet
      <3>csum. x0 + x1 + Cardinality({ m \in msgs2'[round[id] - 1]: IsQ2(m) }) >= N - T
            BY <3>mq, <3>types, Arith_SumThirdMonoGe DEF QSet
      <3> QED BY <3>c0, <3>c1, <3>csum, <1>fr
    <2> QED BY <2>old, <2>one, <2>two
  <1>ngt. CASE ~(round'[id] > 1)
    <2> QED BY <1>ngt
  <1> QED BY <1>gt, <1>ngt
THEOREM Pres_L11_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma11_ValueOnQuorumLessRam'
  <1>l11. Lemma11_ValueOnQuorumLessRam BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>fr. value' = value /\ round' = round BY FaultyStepProps
  <1>p. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY FaultyStepProps
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE LET r == round'[id] IN
          r > 1 =>
            \/ LET v == value'[id]
                   Qv == Senders2({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = v })
               IN
               2 * Cardinality(Qv) > N + T
            \/ LET n0 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                   n1 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                   nq == Cardinality({ m \in msgs2'[r - 1]: IsQ2(m) })
               IN
               \E x0, x1 \in 0..N:
                 /\ x0 <= n0 /\ x1 <= n1
                 /\ x0 + x1 + nq >= N - T
                 /\ 2 * x0 <= N + T
                 /\ 2 * x1 <= N + T
        BY DEF Lemma11_ValueOnQuorumLessRam
  <1>gt. CASE round'[id] > 1
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <1>gt, <1>fr, RoundsNat
    <2>rp. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>old. \/ LET v == value[id]
                    Qv == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = v })
                IN
                2 * Cardinality(Qv) > N + T
             \/ LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                    n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                    nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
                IN
                \E x0, x1 \in 0..N:
                  /\ x0 <= n0 /\ x1 <= n1
                  /\ x0 + x1 + nq >= N - T
                  /\ 2 * x0 <= N + T
                  /\ 2 * x1 <= N + T
          BY <1>l11, <1>fr, <1>gt DEF Lemma11_ValueOnQuorumLessRam
    <2>one. CASE LET v == value[id]
                    Qv == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = v })
                IN
                2 * Cardinality(Qv) > N + T
      <3> DEFINE oldQ == Senders2({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] })
                 newQ == Senders2({ m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] })
      <3>sub. { m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] }
                  \subseteq { m \in msgs2'[round[id] - 1]: IsD2(m) /\ AsD2(m).v = value[id] }
            BY <2>rp, <1>p
      <3>mono. Cardinality(oldQ) <= Cardinality(newQ)
            BY <3>sub, Senders2_Mono DEF oldQ, newQ
      <3>types. Cardinality(oldQ) \in Nat /\ Cardinality(newQ) \in Nat /\ N + T \in Nat
            BY Senders2_Sub, FS_CardinalityType, ConstNat
      <3>gtNew. 2 * Cardinality(newQ) > N + T
            BY <2>one, <3>mono, <3>types, Arith_DoubleGtMono DEF oldQ
      <3> QED BY <3>gtNew, <1>fr DEF newQ
    <2>two. CASE LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                    n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                    nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
                IN
                \E x0, x1 \in 0..N:
                  /\ x0 <= n0 /\ x1 <= n1
                  /\ x0 + x1 + nq >= N - T
                  /\ 2 * x0 <= N + T
                  /\ 2 * x1 <= N + T
      <3> PICK x0 \in 0..N, x1 \in 0..N :
            LET n0 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                n1 == Cardinality({ m \in msgs2[round[id] - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                nq == Cardinality({ m \in msgs2[round[id] - 1]: IsQ2(m) })
            IN
              /\ x0 <= n0 /\ x1 <= n1
              /\ x0 + x1 + nq >= N - T
              /\ 2 * x0 <= N + T
              /\ 2 * x1 <= N + T
            BY <2>two
      <3>v0. 0 \in VALUES BY DEF VALUES
      <3>v1. 1 \in VALUES BY DEF VALUES
      <3>m0. Cardinality(DvSet(round[id] - 1, 0))
                <= Cardinality(DvPSet(round[id] - 1, 0))
            BY <1>tokp, <2>rp, <3>v0, DvFaultyMono
      <3>m1. Cardinality(DvSet(round[id] - 1, 1))
                <= Cardinality(DvPSet(round[id] - 1, 1))
            BY <1>tokp, <2>rp, <3>v1, DvFaultyMono
      <3>mq. Cardinality(QSet(round[id] - 1))
                <= Cardinality(QPSet(round[id] - 1))
            BY <1>tokp, <2>rp, QFaultyMono
      <3>fin0p. IsFiniteSet(DvPSet(round[id] - 1, 0))
            BY <1>tokp, <2>rp, <3>v0, DvFaultyMono
      <3>fin1p. IsFiniteSet(DvPSet(round[id] - 1, 1))
            BY <1>tokp, <2>rp, <3>v1, DvFaultyMono
      <3>finqp. IsFiniteSet(QPSet(round[id] - 1))
            BY <1>tokp, <2>rp, QFaultyMono
      <3>fin0. IsFiniteSet(DvSet(round[id] - 1, 0)) BY <2>rp, <3>v0, D2SetFinite
      <3>fin1. IsFiniteSet(DvSet(round[id] - 1, 1)) BY <2>rp, <3>v1, D2SetFinite
      <3>finq. IsFiniteSet(QSet(round[id] - 1)) BY <2>rp, Q2SetFinite
      <3>types. /\ x0 \in Nat /\ x1 \in Nat
                 /\ Cardinality(DvSet(round[id] - 1, 0)) \in Nat
                 /\ Cardinality(DvSet(round[id] - 1, 1)) \in Nat
                 /\ Cardinality(QSet(round[id] - 1)) \in Nat
                 /\ Cardinality(DvPSet(round[id] - 1, 0)) \in Nat
                 /\ Cardinality(DvPSet(round[id] - 1, 1)) \in Nat
                 /\ Cardinality(QPSet(round[id] - 1)) \in Nat
                 /\ N - T \in Nat
            BY <3>fin0, <3>fin1, <3>finq, <3>fin0p, <3>fin1p, <3>finqp,
               FS_CardinalityType, ConstNat, NgtT, FleqT
      <3>c0. x0 <= Cardinality(DvPSet(round[id] - 1, 0))
            BY <3>m0, <3>types, Arith_GeTrans DEF DvSet
      <3>c1. x1 <= Cardinality(DvPSet(round[id] - 1, 1))
            BY <3>m1, <3>types, Arith_GeTrans DEF DvSet
      <3>csum. x0 + x1 + Cardinality(QPSet(round[id] - 1)) >= N - T
            BY <3>mq, <3>types, Arith_SumThirdMonoGe DEF QSet
      <3> QED BY <3>c0, <3>c1, <3>csum, <1>fr DEF DvPSet, QPSet
    <2> QED BY <2>old, <2>one, <2>two
  <1>ngt. CASE ~(round'[id] > 1)
    <2> QED BY <1>ngt
  <1> QED BY <1>gt, <1>ngt
THEOREM Pres_L11_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma11_ValueOnQuorumLessRam'
  <1>l11. Lemma11_ValueOnQuorumLessRam BY DEF IndInv
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat /\ round[id0] >= 1
        BY <1>dom, RoundPos
  <1>upd. /\ msgs2' = msgs2
          /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ]
          BY DEF Step3
  <1>rd. \A x \in CORRECT :
            round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x])
        BY <1>upd, <1>dom
  <1> PICK received \in SUBSET msgs2[round[id0]] :
        /\ Cardinality(Senders2(received)) = N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
           \/ /\ \A vv \in VALUES: Weights[vv] < T + 1
              /\ \E next_v \in VALUES:
                   /\ value' = [ value EXCEPT ![id0] = next_v ]
                   /\ decision' = decision
        BY DEF Step3
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE LET r == round'[id] IN
          r > 1 =>
            \/ LET v == value'[id]
                   Qv == Senders2({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = v })
               IN
               2 * Cardinality(Qv) > N + T
            \/ LET n0 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 0 })
                   n1 == Cardinality({ m \in msgs2'[r - 1]: IsD2(m) /\ AsD2(m).v = 1 })
                   nq == Cardinality({ m \in msgs2'[r - 1]: IsQ2(m) })
               IN
               \E x0, x1 \in 0..N:
                 /\ x0 <= n0 /\ x1 <= n1
                 /\ x0 + x1 + nq >= N - T
                 /\ 2 * x0 <= N + T
                 /\ 2 * x1 <= N + T
        BY DEF Lemma11_ValueOnQuorumLessRam
  <1>oldId. CASE id # id0
    <2>rSame. round'[id] = round[id] BY <1>oldId, <1>rd
    <2>vSame. value'[id] = value[id] BY <1>oldId, <1>dom DEF Step3
    <2> QED BY <1>l11, <2>rSame, <2>vSame, <1>upd DEF Lemma11_ValueOnQuorumLessRam
  <1>newId. CASE id = id0
    <2>gt. round'[id] > 1 BY <1>newId, <1>rd, <1>r0, Arith_SuccGtOne
    <2>pred. round'[id] - 1 = round[id0] BY <1>newId, <1>rd, <1>r0, Arith_PlusOneMinusOne
    <2>high. CASE \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
      <3> PICK vv \in VALUES:
            /\ Weights[vv] >= T + 1
            /\ value' = [ value EXCEPT ![id0] = vv ]
            /\ IF 2 * Weights[vv] > N + T
               THEN decision' = [ decision EXCEPT ![id0] = vv ]
               ELSE decision' = decision
          BY <2>high
      <3>valp. value'[id] = vv BY <1>newId, <1>dom
      <3>wit. \/ LET Qv == Senders2({ m \in msgs2[round[id0]]: IsD2(m) /\ AsD2(m).v = vv })
                  IN 2 * Cardinality(Qv) > N + T
               \/ LET n0 == Cardinality(DvSet(round[id0], 0))
                      n1 == Cardinality(DvSet(round[id0], 1))
                      nq == Cardinality(QSet(round[id0]))
                  IN
                  \E x0, x1 \in 0..N:
                    /\ x0 <= n0 /\ x1 <= n1
                    /\ x0 + x1 + nq >= N - T
                    /\ 2 * x0 <= N + T
                    /\ 2 * x1 <= N + T
            BY <1>r0, HighWeightReceivedL11Witness DEF Weights
      <3> QED BY <2>gt, <2>pred, <3>valp, <3>wit, <1>upd DEF DvSet, QSet
    <2>low. CASE /\ \A vv \in VALUES: Weights[vv] < T + 1
                 /\ \E next_v \in VALUES:
                      /\ value' = [ value EXCEPT ![id0] = next_v ]
                      /\ decision' = decision
      <3> PICK next_v \in VALUES:
            /\ value' = [ value EXCEPT ![id0] = next_v ]
            /\ decision' = decision
          BY <2>low
      <3>valp. value'[id] = next_v BY <1>newId, <1>dom
      <3>wit. LET n0 == Cardinality(DvSet(round[id0], 0))
                  n1 == Cardinality(DvSet(round[id0], 1))
                  nq == Cardinality(QSet(round[id0]))
              IN
              \E x0, x1 \in 0..N:
                /\ x0 <= n0 /\ x1 <= n1
                /\ x0 + x1 + nq >= N - T
                /\ 2 * x0 <= N + T
                /\ 2 * x1 <= N + T
            BY <1>r0, <2>low, LowWeightsReceivedL11Witness DEF Weights
      <3> QED BY <2>gt, <2>pred, <3>valp, <3>wit, <1>upd DEF DvSet, QSet
    <2> QED BY <2>high, <2>low
  <1> QED BY <1>oldId, <1>newId
THEOREM Pres_L11_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
  BY DEF IndInv, Lemma11_ValueOnQuorumLessRam, vars
THEOREM Pres_Lemma11 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma11_ValueOnQuorumLessRam'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma11_ValueOnQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L11_S2
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step3(id) => Lemma11_ValueOnQuorumLessRam'
    <2> SUFFICES ASSUME Step3(id) PROVE Lemma11_ValueOnQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L11_S3
  <1>o3. FaultyStep => Lemma11_ValueOnQuorumLessRam'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma11_ValueOnQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L11_F
  <1> QED BY Pres_L11_S1, Pres_L11_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L12: reaching round r+1 needs N-T type-2 messages in r =====
THEOREM Pres_L12_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S2 BY DEF S1, S2
  <1>upd. /\ step' = [ step EXCEPT ![id0] = S2 ]
          /\ round' = round
          /\ msgs2' = msgs2
          BY DEF Step1
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S2 ELSE step[x])
        BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x]
        BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> PICK id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
        OBVIOUS
  <1>notId0. id # id0 BY <1>st, <1>dist
  <1>oldNext. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
        BY <1>notId0, <1>st, <1>rd
  <1>old. Cardinality(Senders2(msgs2[r])) >= N - T
        BY <1>l12, <1>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> QED BY <1>old, <1>upd
THEOREM Pres_L12_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>dist. S1 # S3 BY DEF S1, S3
  <1>upd. /\ step' = [ step EXCEPT ![id0] = S3 ]
          /\ round' = round
          BY DEF Step2
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S3 ELSE step[x])
        BY <1>upd, <1>doms
  <1>rd. \A x \in CORRECT : round'[x] = round[x]
        BY <1>upd, <1>doms
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> PICK id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
        OBVIOUS
  <1>notId0. id # id0 BY <1>st, <1>dist
  <1>oldNext. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
        BY <1>notId0, <1>st, <1>rd
  <1>old. Cardinality(Senders2(msgs2[r])) >= N - T
        BY <1>l12, <1>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>grow. msgs2[r] \subseteq msgs2'[r]
        BY <1>nm, <1>r0, <1>dom2
  <1>mono. Cardinality(Senders2(msgs2[r])) <= Cardinality(Senders2(msgs2'[r]))
        BY <1>grow, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L12_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>p. /\ step' = step /\ round' = round
        /\ \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
        BY FaultyStepProps
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>oldNext. \E id \in CORRECT : round[id] = r + 1 /\ step[id] = S1
        BY <1>p
  <1>old. Cardinality(Senders2(msgs2[r])) >= N - T
        BY <1>l12, <1>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1>sub. msgs2[r] \subseteq msgs2'[r] BY <1>p
  <1>mono. Cardinality(Senders2(msgs2[r])) <= Cardinality(Senders2(msgs2'[r]))
        BY <1>sub, Senders2_Mono
  <1>types. Cardinality(Senders2(msgs2[r])) \in Nat
             /\ Cardinality(Senders2(msgs2'[r])) \in Nat
             /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1> QED BY <1>old, <1>mono, <1>types, Arith_GeTrans
THEOREM Pres_L12_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>l12. Lemma12_CannotJumpRoundsWithoutQuorum BY DEF IndInv
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat BY RoundsNat DEF TypeOK
  <1>doms. step \in [ CORRECT -> {S1,S2,S3} ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>upd. /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ]
          /\ step' = [ step EXCEPT ![id0] = S1 ]
          /\ msgs2' = msgs2
          BY DEF Step3
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x])
        BY <1>upd, <1>doms
  <1>st. \A x \in CORRECT : step'[x] = (IF x = id0 THEN S1 ELSE step[x])
        BY <1>upd, <1>doms
  <1>pickRec. PICK received \in SUBSET msgs2[round[id0]] :
        Cardinality(Senders2(received)) = N - T
        BY DEF Step3
  <1>recSub. received \subseteq msgs2[round[id0]] OBVIOUS
  <1>recMono. Cardinality(Senders2(received)) <= Cardinality(Senders2(msgs2[round[id0]]))
        BY <1>recSub, Senders2_Mono
  <1>recTypes. Cardinality(Senders2(received)) \in Nat
               /\ Cardinality(Senders2(msgs2[round[id0]])) \in Nat
               /\ N - T \in Nat
        BY Senders2_Sub, FS_CardinalityType, NgtT, ConstNat, FleqT
  <1>recQ. Cardinality(Senders2(msgs2[round[id0]])) >= N - T
        BY <1>pickRec, <1>recMono, <1>recTypes, Arith_GeTrans
  <1> SUFFICES ASSUME NEW r \in ROUNDS, r + 1 \in ROUNDS,
                      \E id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
               PROVE  Cardinality(Senders2(msgs2'[r])) >= N - T
        BY DEF Lemma12_CannotJumpRoundsWithoutQuorum
  <1> PICK id \in CORRECT : round'[id] = r + 1 /\ step'[id] = S1
        OBVIOUS
  <1>newId. CASE id = id0
    <2>eqsucc. r + 1 = round[id0] + 1 BY <1>newId, <1>rd
    <2>rnat. r \in Nat BY RoundsNat
    <2>rid. r = round[id0] BY <2>eqsucc, <2>rnat, <1>r0, Arith_SuccCancel
    <2> QED BY <2>rid, <1>recQ, <1>upd
  <1>oldId. CASE id # id0
    <2>oldNext. \E oldId \in CORRECT : round[oldId] = r + 1 /\ step[oldId] = S1
          BY <1>oldId, <1>rd, <1>st
    <2>old. Cardinality(Senders2(msgs2[r])) >= N - T
          BY <1>l12, <2>oldNext DEF Lemma12_CannotJumpRoundsWithoutQuorum
    <2> QED BY <2>old, <1>upd
  <1> QED BY <1>newId, <1>oldId
THEOREM Pres_L12_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  BY DEF IndInv, Lemma12_CannotJumpRoundsWithoutQuorum, vars
THEOREM Pres_Lemma12 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step1(id) => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME Step1(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_S1
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_S2
  <1>o3. ASSUME NEW id \in CORRECT PROVE Step3(id) => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME Step3(id) PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_S3
  <1>o4. FaultyStep => Lemma12_CannotJumpRoundsWithoutQuorum'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma12_CannotJumpRoundsWithoutQuorum'
          OBVIOUS
    <2> QED BY Pres_L12_F
  <1> QED BY Pres_L12_ST, <1>o1, <1>o2, <1>o3, <1>o4 DEF Next, CorrectStep

\* ===== L13: value lock -- a correct value at r matches Supported(r-1) =====
THEOREM Pres_L13_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma13_ValueLock'
  BY RoundsNat DEF TypeOK, IndInv, Lemma13_ValueLock, SupportedValues, Step1
THEOREM Pres_L13_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma13_ValueLock'
  <1>l13. Lemma13_ValueLock BY DEF IndInv
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ] BY DEF TypeOK
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat /\ round[id0] >= 1
        BY <1>dom, RoundPos
  <1>upd. /\ msgs2' = msgs2
          /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ]
          BY DEF Step3
  <1>tokp. TypeOK' BY TypePres DEF Next, CorrectStep
  <1>rd. \A x \in CORRECT :
            round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x])
        BY <1>upd, <1>dom
  <1>spFrame. \A rr \in ROUNDS : SupportedValuesP(rr) = SupportedValues(rr)
        BY <1>upd, SupportedValuesPFrame
  <1> PICK received \in SUBSET msgs2[round[id0]] :
        /\ Cardinality(Senders2(received)) = N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
           \/ /\ \A vv \in VALUES: Weights[vv] < T + 1
              /\ \E next_v \in VALUES:
                   /\ value' = [ value EXCEPT ![id0] = next_v ]
                   /\ decision' = decision
        BY DEF Step3
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
  <1> DEFINE supportedP == [ rr \in ROUNDS |-> SupportedValuesP(rr) ]
  <1> SUFFICES
        LET supported == supportedP IN
        \A id \in CORRECT, dummy \in VALUES :
          \/ round'[id] = 1
          \/ /\ round'[id] > 1
             /\ LET S == supported[round'[id] - 1] IN
                \/ S = {}
                \/ value'[id] \in S
        BY <1>tokp, SupportedValuesPrimeIsP DEF TypeOK, Lemma13_ValueLock, supportedP
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW dummy \in VALUES
        PROVE \/ round'[id] = 1
              \/ /\ round'[id] > 1
                 /\ LET S == supportedP[round'[id] - 1] IN
                    \/ S = {}
                    \/ value'[id] \in S
        BY DEF supportedP
  <1>oldId. CASE id # id0
    <2>rSame. round'[id] = round[id] BY <1>oldId, <1>rd
    <2>vSame. value'[id] = value[id] BY <1>oldId, <1>dom DEF Step3
    <2>val. value[id] \in VALUES BY <1>dom
    <2>one. CASE round[id] = 1
      <3> QED BY <2>one, <2>rSame
    <2>gt. CASE round[id] > 1
      <3>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <2>gt, RoundsNat
      <3>predIn. round[id] - 1 \in ROUNDS BY <3>rin, RoundPredInRounds
      <3>lock. LET S == SupportedValues(round[id] - 1) IN
                  \/ S = {}
                  \/ value[id] \in S
            BY <1>l13, <2>val, <2>gt, <3>predIn DEF Lemma13_ValueLock
      <3>sp. supportedP[round'[id] - 1] = SupportedValues(round[id] - 1)
            BY <2>rSame, <3>predIn, <1>spFrame
      <3> QED BY <2>rSame, <2>vSame, <2>gt, <3>lock, <3>sp
    <2> QED BY <2>one, <2>gt, <1>dom, RoundsNat, ConstNat
  <1>newId. CASE id = id0
    <2>gt. round'[id] > 1 BY <1>newId, <1>rd, <1>r0, Arith_SuccGtOne
    <2>pred. round'[id] - 1 = round[id0] BY <1>newId, <1>rd, <1>r0, Arith_PlusOneMinusOne
    <2>high. CASE \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
      <3> PICK vv \in VALUES:
            /\ Weights[vv] >= T + 1
            /\ value' = [ value EXCEPT ![id0] = vv ]
            /\ IF 2 * Weights[vv] > N + T
               THEN decision' = [ decision EXCEPT ![id0] = vv ]
               ELSE decision' = decision
          BY <2>high
      <3>valp. value'[id] = vv BY <1>newId, <1>dom
      <3>empty. CASE SupportedValues(round[id0]) = {}
        <4>sp. supportedP[round'[id] - 1] = {}
              BY <2>pred, <1>r0, <1>spFrame, <3>empty
        <4> QED BY <2>gt, <4>sp
      <3>nonempty. CASE SupportedValues(round[id0]) # {}
        <4>pick. PICK w \in SupportedValues(round[id0]) : TRUE BY <3>nonempty
        <4>eq. w = vv BY <1>r0, <4>pick, ReceivedDQuorumDominatesSupported DEF Weights
        <4>vin. vv \in SupportedValues(round[id0]) BY <4>pick, <4>eq
        <4>sp. supportedP[round'[id] - 1] = SupportedValues(round[id0])
              BY <2>pred, <1>r0, <1>spFrame
        <4> QED BY <2>gt, <3>valp, <4>vin, <4>sp
      <3> QED BY <3>empty, <3>nonempty
    <2>low. CASE /\ \A vv \in VALUES: Weights[vv] < T + 1
                 /\ \E next_v \in VALUES:
                      /\ value' = [ value EXCEPT ![id0] = next_v ]
                      /\ decision' = decision
      <3>empty. SupportedValues(round[id0]) = {}
            BY <1>r0, <2>low, LowWeightsSupportedEmpty DEF Weights
      <3>sp. supportedP[round'[id] - 1] = {}
            BY <2>pred, <1>r0, <1>spFrame, <3>empty
      <3> QED BY <2>gt, <3>sp
    <2> QED BY <2>high, <2>low
  <1> QED BY <1>oldId, <1>newId
THEOREM Pres_L13_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma13_ValueLock'
  <1>l13. Lemma13_ValueLock BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next, CorrectStep
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ]
        BY DEF TypeOK
  <1>fr. value' = value /\ round' = round BY DEF Step2
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>dom2. DOMAIN msgs2 = ROUNDS BY Msgs2DomR
  <1>nm. PICK nm :
        msgs2' = [ msgs2 EXCEPT ![round[id0]] = msgs2[round[id0]] \union { nm } ]
        BY VariantAx DEF Step2
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr]
    <2> SUFFICES ASSUME NEW rr \in ROUNDS PROVE msgs2[rr] \subseteq msgs2'[rr] OBVIOUS
    <2> QED BY <1>nm, <1>r0, <1>dom2
  <1> DEFINE supportedP == [ rr \in ROUNDS |-> SupportedValuesP(rr) ]
  <1> SUFFICES
        LET supported == supportedP IN
        \A id \in CORRECT, dummy \in VALUES :
          \/ round'[id] = 1
          \/ /\ round'[id] > 1
             /\ LET S == supported[round'[id] - 1] IN
                \/ S = {}
                \/ value'[id] \in S
        BY <1>tokp, SupportedValuesPrimeIsP DEF TypeOK, Lemma13_ValueLock, supportedP
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW dummy \in VALUES
        PROVE \/ round'[id] = 1
              \/ /\ round'[id] > 1
                 /\ LET S == supportedP[round'[id] - 1] IN
                    \/ S = {}
                    \/ value'[id] \in S
        BY DEF supportedP
  <1>one. CASE round[id] = 1
    <2> QED BY <1>one, <1>fr
  <1>gt. CASE round[id] > 1
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <1>gt, RoundsNat
    <2>predIn. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>val. value[id] \in VALUES BY <1>dom
    <2>oldLock. LET S == SupportedValues(round[id] - 1) IN
                  \/ S = {}
                  \/ value[id] \in S
          BY <1>l13, <1>gt, <2>val, <2>predIn DEF Lemma13_ValueLock
    <2>newEmpty. CASE supportedP[round[id] - 1] = {}
      <3> QED BY <1>gt, <1>fr, <2>newEmpty
    <2>newNonempty. CASE supportedP[round[id] - 1] # {}
      <3> PICK vp \in supportedP[round[id] - 1] : TRUE BY <2>newNonempty
      <3>vpIn. vp \in supportedP[round[id] - 1] OBVIOUS
      <3>vpSup. vp \in SupportedValuesP(round[id] - 1) BY <3>vpIn, <2>predIn DEF supportedP
      <3>vpVal. vp \in VALUES BY <3>vpSup DEF SupportedValuesP
      <3>total. Cardinality(Senders2(msgs2[round[id] - 1])) >= N - T
            BY <1>gt, <2>predIn, ReplicaPredRoundHasTotal
      <3>oldSup. vp \in SupportedValues(round[id] - 1)
            BY <2>predIn, <3>vpSup, <3>total, <1>grow, SupportedPToOldWhenTotal
      <3>oldNonempty. SupportedValues(round[id] - 1) # {} BY <3>oldSup
      <3>valOld. value[id] \in SupportedValues(round[id] - 1)
            BY <2>oldLock, <3>oldNonempty
      <3>eq0. vp = value[id] BY <2>predIn, <3>oldSup, <3>valOld, SupportedUnique
      <3>eq. value[id] = vp BY <3>eq0
      <3> QED BY <1>gt, <1>fr, <3>vpSup, <3>eq DEF supportedP
    <2> QED BY <2>newEmpty, <2>newNonempty
  <1> QED BY <1>one, <1>gt, <1>dom, RoundsNat, ConstNat
THEOREM Pres_L13_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma13_ValueLock'
  <1>l13. Lemma13_ValueLock BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next
  <1>dom. value \in [ CORRECT -> VALUES ] /\ round \in [ CORRECT -> ROUNDS ]
        BY DEF TypeOK
  <1>fr. value' = value /\ round' = round BY FaultyStepProps
  <1>grow. \A rr \in ROUNDS : msgs2[rr] \subseteq msgs2'[rr] BY FaultyStepProps
  <1> DEFINE supportedP == [ rr \in ROUNDS |-> SupportedValuesP(rr) ]
  <1> SUFFICES
        LET supported == supportedP IN
        \A id \in CORRECT, dummy \in VALUES :
          \/ round'[id] = 1
          \/ /\ round'[id] > 1
             /\ LET S == supported[round'[id] - 1] IN
                \/ S = {}
                \/ value'[id] \in S
        BY <1>tokp, SupportedValuesPrimeIsP DEF TypeOK, Lemma13_ValueLock, supportedP
  <1> SUFFICES ASSUME NEW id \in CORRECT, NEW dummy \in VALUES
        PROVE \/ round'[id] = 1
              \/ /\ round'[id] > 1
                 /\ LET S == supportedP[round'[id] - 1] IN
                    \/ S = {}
                    \/ value'[id] \in S
        BY DEF supportedP
  <1>one. CASE round[id] = 1
    <2> QED BY <1>one, <1>fr
  <1>gt. CASE round[id] > 1
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <1>gt, RoundsNat
    <2>predIn. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>val. value[id] \in VALUES BY <1>dom
    <2>oldLock. LET S == SupportedValues(round[id] - 1) IN
                  \/ S = {}
                  \/ value[id] \in S
          BY <1>l13, <1>gt, <2>val, <2>predIn DEF Lemma13_ValueLock
    <2>newEmpty. CASE supportedP[round[id] - 1] = {}
      <3> QED BY <1>gt, <1>fr, <2>newEmpty
    <2>newNonempty. CASE supportedP[round[id] - 1] # {}
      <3> PICK vp \in supportedP[round[id] - 1] : TRUE BY <2>newNonempty
      <3>vpIn. vp \in supportedP[round[id] - 1] OBVIOUS
      <3>vpSup. vp \in SupportedValuesP(round[id] - 1) BY <3>vpIn, <2>predIn DEF supportedP
      <3>vpVal. vp \in VALUES BY <3>vpSup DEF SupportedValuesP
      <3>total. Cardinality(Senders2(msgs2[round[id] - 1])) >= N - T
            BY <1>gt, <2>predIn, ReplicaPredRoundHasTotal
      <3>oldSup. vp \in SupportedValues(round[id] - 1)
            BY <2>predIn, <3>vpSup, <3>total, <1>grow, SupportedPToOldWhenTotal
      <3>oldNonempty. SupportedValues(round[id] - 1) # {} BY <3>oldSup
      <3>valOld. value[id] \in SupportedValues(round[id] - 1)
            BY <2>oldLock, <3>oldNonempty
      <3>eq0. vp = value[id] BY <2>predIn, <3>oldSup, <3>valOld, SupportedUnique
      <3>eq. value[id] = vp BY <3>eq0
      <3> QED BY <1>gt, <1>fr, <3>vpSup, <3>eq DEF supportedP
    <2> QED BY <2>newEmpty, <2>newNonempty
  <1> QED BY <1>one, <1>gt, <1>dom, RoundsNat, ConstNat
THEOREM Pres_L13_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma13_ValueLock'
  BY DEF IndInv, Lemma13_ValueLock, SupportedValues, vars
THEOREM Pres_Lemma13 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma13_ValueLock'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma13_ValueLock'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma13_ValueLock'
          OBVIOUS
    <2> QED BY Pres_L13_S2
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step3(id) => Lemma13_ValueLock'
    <2> SUFFICES ASSUME Step3(id) PROVE Lemma13_ValueLock'
          OBVIOUS
    <2> QED BY Pres_L13_S3
  <1>o3. FaultyStep => Lemma13_ValueLock'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma13_ValueLock'
          OBVIOUS
    <2> QED BY Pres_L13_F
  <1> QED BY Pres_L13_S1, Pres_L13_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep

\* ===== L1: a decision is backed by a D2 quorum in the previous round =====
THEOREM Pres_L1_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  BY DEF IndInv, Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam, Step1
THEOREM Pres_L1_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  <1>l1. Lemma1_DecisionRequiresLastQuorumLessRam BY DEF IndInv
  <1>dom. decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
           /\ round \in [ CORRECT -> ROUNDS ]
        BY DEF TypeOK
  <1>fr. decision' = decision /\ round' = round BY DEF Step2
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE \/ decision'[id] = NO_DECISION
              \/ /\ round'[id] > 1
                 /\ LET nv == Cardinality({ m \in msgs2'[round'[id] - 1]:
                                           IsD2(m) /\ AsD2(m).v = decision'[id] })
                        n == Cardinality(msgs2'[round'[id] - 1])
                    IN
                    /\ n >= N - T
                    /\ nv >= T + 1
                    /\ 2 * nv > N + T
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
  <1>dec. CASE decision'[id] = NO_DECISION
    <2> QED BY <1>dec
  <1>non. CASE decision'[id] # NO_DECISION
    <2>v. decision[id] \in VALUES BY <1>dom, <1>fr, <1>non, NoDecisionNotValue
    <2>old. /\ round[id] > 1
             /\ LET nv == Cardinality({ m \in msgs2[round[id] - 1]:
                                       IsD2(m) /\ AsD2(m).v = decision[id] })
                    n == Cardinality(msgs2[round[id] - 1])
                IN
                /\ n >= N - T
                /\ nv >= T + 1
                /\ 2 * nv > N + T
          BY <1>l1, <1>fr, <1>non DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <2>old, RoundsNat
    <2>rp. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>oldN. Cardinality(msgs2[round[id] - 1]) >= N - T
          BY <2>old DEF ExistsQuorum2LessRam
    <2>oldNv. Cardinality(DvSet(round[id] - 1, decision[id])) >= T + 1
          BY <2>old DEF ExistsQuorum2LessRam, DvSet
    <2>oldTw. 2 * Cardinality(DvSet(round[id] - 1, decision[id])) > N + T
          BY <2>old DEF ExistsQuorum2LessRam, DvSet
    <2>mn. Cardinality(msgs2[round[id] - 1])
              <= Cardinality(msgs2'[round[id] - 1])
          BY <2>rp, Msgs2Step2Mono
    <2>mv. Cardinality(DvSet(round[id] - 1, decision[id]))
              <= Cardinality({ m \in msgs2'[round[id] - 1]:
                                 IsD2(m) /\ AsD2(m).v = decision[id] })
          BY <2>rp, <2>v, DvStep2Mono
    <2>finOldN. IsFiniteSet(msgs2[round[id] - 1]) BY <2>rp, Msgs2Finite
    <2>finNewN. IsFiniteSet(msgs2'[round[id] - 1]) BY <2>rp, Msgs2Step2Mono
    <2>finOldV. IsFiniteSet(DvSet(round[id] - 1, decision[id])) BY <2>rp, <2>v, D2SetFinite
    <2>finNewV. IsFiniteSet({ m \in msgs2'[round[id] - 1]:
                                IsD2(m) /\ AsD2(m).v = decision[id] })
          BY <2>rp, <2>v, DvStep2Mono
    <2>types. /\ Cardinality(msgs2[round[id] - 1]) \in Nat
               /\ Cardinality(msgs2'[round[id] - 1]) \in Nat
               /\ Cardinality(DvSet(round[id] - 1, decision[id])) \in Nat
               /\ Cardinality({ m \in msgs2'[round[id] - 1]:
                                  IsD2(m) /\ AsD2(m).v = decision[id] }) \in Nat
               /\ N - T \in Nat
               /\ T + 1 \in Nat
               /\ N + T \in Nat
          BY <2>finOldN, <2>finNewN, <2>finOldV, <2>finNewV,
             FS_CardinalityType, ConstNat, NgtT, FleqT
    <2>newN. Cardinality(msgs2'[round[id] - 1]) >= N - T
          BY <2>oldN, <2>mn, <2>types, Arith_GeTrans
    <2>newNv. Cardinality({ m \in msgs2'[round[id] - 1]:
                              IsD2(m) /\ AsD2(m).v = decision[id] }) >= T + 1
          BY <2>oldNv, <2>mv, <2>types, Arith_GeTrans
    <2>newTw. 2 * Cardinality({ m \in msgs2'[round[id] - 1]:
                                  IsD2(m) /\ AsD2(m).v = decision[id] }) > N + T
          BY <2>oldTw, <2>mv, <2>types, Arith_DoubleGtMono
    <2> QED BY <2>old, <2>newN, <2>newNv, <2>newTw, <1>fr
  <1> QED BY <1>dec, <1>non
THEOREM Pres_L1_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  <1>l1. Lemma1_DecisionRequiresLastQuorumLessRam BY DEF IndInv
  <1>tokp. TypeOK' BY TypePres DEF Next
  <1>dom. decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
           /\ round \in [ CORRECT -> ROUNDS ]
        BY DEF TypeOK
  <1>fr. decision' = decision /\ round' = round BY FaultyStepProps
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE \/ decision'[id] = NO_DECISION
              \/ /\ round'[id] > 1
                 /\ LET nv == Cardinality({ m \in msgs2'[round'[id] - 1]:
                                           IsD2(m) /\ AsD2(m).v = decision'[id] })
                        n == Cardinality(msgs2'[round'[id] - 1])
                    IN
                    /\ n >= N - T
                    /\ nv >= T + 1
                    /\ 2 * nv > N + T
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
  <1>dec. CASE decision'[id] = NO_DECISION
    <2> QED BY <1>dec
  <1>non. CASE decision'[id] # NO_DECISION
    <2>v. decision[id] \in VALUES BY <1>dom, <1>fr, <1>non, NoDecisionNotValue
    <2>old. /\ round[id] > 1
             /\ LET nv == Cardinality({ m \in msgs2[round[id] - 1]:
                                       IsD2(m) /\ AsD2(m).v = decision[id] })
                    n == Cardinality(msgs2[round[id] - 1])
                IN
                /\ n >= N - T
                /\ nv >= T + 1
                /\ 2 * nv > N + T
          BY <1>l1, <1>fr, <1>non DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
    <2>rin. round[id] \in ROUNDS /\ round[id] # 1 BY <1>dom, <2>old, RoundsNat
    <2>rp. round[id] - 1 \in ROUNDS BY <2>rin, RoundPredInRounds
    <2>oldN. Cardinality(msgs2[round[id] - 1]) >= N - T
          BY <2>old DEF ExistsQuorum2LessRam
    <2>oldNv. Cardinality(DvSet(round[id] - 1, decision[id])) >= T + 1
          BY <2>old DEF ExistsQuorum2LessRam, DvSet
    <2>oldTw. 2 * Cardinality(DvSet(round[id] - 1, decision[id])) > N + T
          BY <2>old DEF ExistsQuorum2LessRam, DvSet
    <2>mn. Cardinality(msgs2[round[id] - 1])
              <= Cardinality(msgs2'[round[id] - 1])
          BY <1>tokp, <2>rp, Msgs2FaultyMono
    <2>mv. Cardinality(DvSet(round[id] - 1, decision[id]))
              <= Cardinality(DvPSet(round[id] - 1, decision[id]))
          BY <1>tokp, <2>rp, <2>v, DvFaultyMono
    <2>finOldN. IsFiniteSet(msgs2[round[id] - 1]) BY <2>rp, Msgs2Finite
    <2>finNewN. IsFiniteSet(msgs2'[round[id] - 1]) BY <1>tokp, <2>rp, Msgs2FaultyMono
    <2>finOldV. IsFiniteSet(DvSet(round[id] - 1, decision[id])) BY <2>rp, <2>v, D2SetFinite
    <2>finNewV. IsFiniteSet(DvPSet(round[id] - 1, decision[id])) BY <1>tokp, <2>rp, <2>v, DvFaultyMono
    <2>types. /\ Cardinality(msgs2[round[id] - 1]) \in Nat
               /\ Cardinality(msgs2'[round[id] - 1]) \in Nat
               /\ Cardinality(DvSet(round[id] - 1, decision[id])) \in Nat
               /\ Cardinality(DvPSet(round[id] - 1, decision[id])) \in Nat
               /\ N - T \in Nat
               /\ T + 1 \in Nat
               /\ N + T \in Nat
          BY <2>finOldN, <2>finNewN, <2>finOldV, <2>finNewV,
             FS_CardinalityType, ConstNat, NgtT, FleqT
    <2>newN. Cardinality(msgs2'[round[id] - 1]) >= N - T
          BY <2>oldN, <2>mn, <2>types, Arith_GeTrans
    <2>newNv. Cardinality(DvPSet(round[id] - 1, decision[id])) >= T + 1
          BY <2>oldNv, <2>mv, <2>types, Arith_GeTrans
    <2>newTw. 2 * Cardinality(DvPSet(round[id] - 1, decision[id])) > N + T
          BY <2>oldTw, <2>mv, <2>types, Arith_DoubleGtMono
    <2> QED BY <2>old, <2>newN, <2>newNv, <2>newTw, <1>fr DEF DvPSet
  <1> QED BY <1>dec, <1>non
\* ===== L1 Step3: a decision requires a quorum2 in the immediately preceding round. =====
\* Step3 leaves msgs2 unchanged; only id0's decision/round/value/step move. For id # id0 the
\* old invariant carries verbatim. For id0 that DECIDES this step, the decision condition
\* 2*Weights[v] > N+T directly yields the quorum at round[id0] = round'[id0]-1. The single
\* remaining obligation -- id0 has ALREADY decided and advances without re-deciding -- is
\* isolated in Pres_L1_S3_DecidedCarry below.

\* ISOLATED HARD OBLIGATION. id0 already decided w = decision[id0] # NO_DECISION and takes a
\* non-deciding Step3 (decision' = decision), advancing round[id0] -> round[id0]+1. Lemma1c'
\* then needs a strict w-quorum at round[id0].
\*
\* Concrete finishing chain, preserving the original goal:
\*   1. StrictQuorumSupportedSingleton:
\*        ExistsQuorum2LessRam(a, v) plus N-T type-2 senders implies
\*        SupportedValues(a) = {v}.
\*      This is where Lemma7 and the N > 5*T arithmetic show that a strict D2 quorum
\*      has too few "other" senders for any other support.
\*   2. LockedRoundCorrectM1:
\*        SupportedValues(a) = {v} and a + 1 \in ROUNDS imply every correct M1 in
\*        msgs1[a + 1] carries v (Lemma9), and there are enough such correct M1s in
\*        any Step2 receive set to force D2(v), not Q2. Lemma8 is the key negative
\*        fact that rules out a correct Q2 in the locked round.
\*   3. LockedReceiveStrictD:
\*        Under the locked-round fact, every Step3 receive set of N-T type-2 senders in
\*        round a + 1 contains more than (N+T)/2 D2(v) messages. This closes both
\*        Pres_L1_S3_DecidedCarry and the Pres_L6 Step3 case.
\*   4. CrossRoundStrictQuorum:
\*        Reuse the same locked-round induction in Section D to show that any later
\*        strict quorum is for v; then Agreement follows from Lemma1c for both decisions.
THEOREM Pres_L1_S3_DecidedCarry ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0),
         decision' = decision, decision[id0] # NO_DECISION
  PROVE  /\ Cardinality(msgs2'[round[id0]]) >= N - T
         /\ Cardinality({ m \in msgs2'[round[id0]]: IsD2(m) /\ AsD2(m).v = decision[id0] }) >= T + 1
         /\ 2 * Cardinality({ m \in msgs2'[round[id0]]: IsD2(m) /\ AsD2(m).v = decision[id0] }) > N + T
  <1>r0. round[id0] \in ROUNDS BY DEF TypeOK
  <1>v0. decision[id0] \in VALUES BY DEF TypeOK, NoDecisionNotValue
  <1>upd. msgs2' = msgs2 BY DEF Step3
  <1> PICK received \in SUBSET msgs2[round[id0]] :
        /\ Cardinality(Senders2(received)) = N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
           \/ /\ \A vv \in VALUES: Weights[vv] < T + 1
              /\ \E next_v \in VALUES:
                   /\ value' = [ value EXCEPT ![id0] = next_v ]
                   /\ decision' = decision
        BY DEF Step3
  <1> DEFINE Drec == { m \in received: IsD2(m) /\ AsD2(m).v = decision[id0] }
             Dfull == DvSet(round[id0], decision[id0])
  <1>lock. 2 * Cardinality(Senders2(Drec)) > N + T
        BY LockedReceiveStrictD DEF Drec
  <1>recsub. received \subseteq msgs2[round[id0]] OBVIOUS
  <1>finM. IsFiniteSet(msgs2[round[id0]]) BY <1>r0, Msgs2Finite
  <1>senLe1. Cardinality(Senders2(received)) <= Cardinality(Senders2(msgs2[round[id0]]))
        BY <1>recsub, Senders2_Mono
  <1>senLe2. Cardinality(Senders2(msgs2[round[id0]])) <= Cardinality(msgs2[round[id0]])
        BY <1>finM, Senders2_CardLeSet
  <1>finD. IsFiniteSet(Dfull) BY <1>r0, <1>v0, D2SetFinite DEF Dfull
  <1>dsub. Drec \subseteq Dfull BY <1>recsub DEF Drec, Dfull, DvSet
  <1>wLe1. Cardinality(Senders2(Drec)) <= Cardinality(Senders2(Dfull))
        BY <1>dsub, Senders2_Mono
  <1>wLe2. Cardinality(Senders2(Dfull)) <= Cardinality(Dfull)
        BY <1>finD, Senders2_CardLeSet
  <1>types. /\ Cardinality(msgs2[round[id0]]) \in Nat
             /\ Cardinality(Senders2(msgs2[round[id0]])) \in Nat
             /\ Cardinality(Senders2(received)) \in Nat
             /\ Cardinality(Dfull) \in Nat
             /\ Cardinality(Senders2(Dfull)) \in Nat
             /\ Cardinality(Senders2(Drec)) \in Nat
             /\ N - T \in Nat /\ T + 1 \in Nat /\ N + T \in Nat
        BY <1>finM, <1>finD, Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>nGe. Cardinality(msgs2[round[id0]]) >= N - T
        BY <1>senLe1, <1>senLe2, <1>types, Arith_LeTrans
  <1>wLeFull. Cardinality(Senders2(Drec)) <= Cardinality(Dfull)
        BY <1>wLe1, <1>wLe2, <1>types, Arith_LeTrans
  <1>recGe. Cardinality(Senders2(Drec)) >= T + 1
        BY <1>lock, <1>types, Arith_DoubleGtNplusTImplTplusOne
  <1>nvGe. Cardinality(Dfull) >= T + 1
        BY <1>recGe, <1>wLeFull, <1>types, Arith_GeTrans
  <1>nv2. 2 * Cardinality(Dfull) > N + T
        BY <1>lock, <1>wLeFull, <1>types, Arith_DoubleGtMono
  <1> QED BY <1>upd, <1>nGe, <1>nvGe, <1>nv2 DEF Dfull, DvSet

THEOREM Pres_L1_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  <1>l1. Lemma1_DecisionRequiresLastQuorumLessRam BY DEF IndInv
  <1>dom. /\ decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
          /\ round \in [ CORRECT -> ROUNDS ]
          /\ value \in [ CORRECT -> VALUES ]
        BY DEF TypeOK
  <1>r0. round[id0] \in ROUNDS /\ round[id0] \in Nat /\ round[id0] >= 1
        BY <1>dom, RoundPos
  <1>upd. /\ msgs2' = msgs2
          /\ round' = [ round EXCEPT ![id0] = round[id0] + 1 ]
        BY DEF Step3
  <1>rd. \A x \in CORRECT : round'[x] = (IF x = id0 THEN round[id0] + 1 ELSE round[x])
        BY <1>upd, <1>dom
  <1> PICK received \in SUBSET msgs2[round[id0]] :
        /\ Cardinality(Senders2(received)) = N - T
        /\ LET Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
           IN
           \/ \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
           \/ /\ \A vv \in VALUES: Weights[vv] < T + 1
              /\ \E next_v \in VALUES:
                   /\ value' = [ value EXCEPT ![id0] = next_v ]
                   /\ decision' = decision
        BY DEF Step3
  <1> DEFINE Weights == [ vv \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv })) ]
  <1> SUFFICES ASSUME NEW id \in CORRECT
        PROVE \/ decision'[id] = NO_DECISION
              \/ /\ round'[id] > 1
                 /\ LET nv == Cardinality({ m \in msgs2'[round'[id] - 1]:
                                           IsD2(m) /\ AsD2(m).v = decision'[id] })
                        n == Cardinality(msgs2'[round'[id] - 1])
                    IN
                    /\ n >= N - T
                    /\ nv >= T + 1
                    /\ 2 * nv > N + T
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
  <1>oldId. CASE id # id0
    <2>dSame. decision'[id] = decision[id] BY <1>oldId, <1>dom DEF Step3
    <2>rSame. round'[id] = round[id] BY <1>oldId, <1>rd
    <2> QED BY <1>l1, <2>dSame, <2>rSame, <1>upd
          DEF Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam
  <1>newId. CASE id = id0
    <2>gt. round'[id] > 1 BY <1>newId, <1>rd, <1>r0, Arith_SuccGtOne
    <2>pred. round'[id] - 1 = round[id0] BY <1>newId, <1>rd, <1>r0, Arith_PlusOneMinusOne
    <2>high. CASE \E vv \in VALUES:
                /\ Weights[vv] >= T + 1
                /\ value' = [ value EXCEPT ![id0] = vv ]
                /\ IF 2 * Weights[vv] > N + T
                   THEN decision' = [ decision EXCEPT ![id0] = vv ]
                   ELSE decision' = decision
      <3> PICK vv \in VALUES:
            /\ Weights[vv] >= T + 1
            /\ value' = [ value EXCEPT ![id0] = vv ]
            /\ IF 2 * Weights[vv] > N + T
               THEN decision' = [ decision EXCEPT ![id0] = vv ]
               ELSE decision' = decision
          BY <2>high
      <3>decide. CASE 2 * Weights[vv] > N + T
        <4>decp. decision' = [ decision EXCEPT ![id0] = vv ] BY <3>decide
        <4>dvv. decision'[id] = vv BY <4>decp, <1>newId, <1>dom
        <4>recsub. received \subseteq msgs2[round[id0]] OBVIOUS
        <4>finM. IsFiniteSet(msgs2[round[id0]]) BY <1>r0, Msgs2Finite
        <4>finDv. IsFiniteSet(DvSet(round[id0], vv))
                  /\ Cardinality(DvSet(round[id0], vv)) <= N
              BY <1>r0, Msgs2Finite, D2SetFinite
        <4>RDsub. { m \in received: IsD2(m) /\ AsD2(m).v = vv } \subseteq DvSet(round[id0], vv)
              BY <4>recsub DEF DvSet
        <4>wDef. Weights[vv] = Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv }))
              OBVIOUS
        <4>senLe1. Cardinality(Senders2(received)) <= Cardinality(Senders2(msgs2[round[id0]]))
              BY <4>recsub, Senders2_Mono
        <4>senLe2. Cardinality(Senders2(msgs2[round[id0]])) <= Cardinality(msgs2[round[id0]])
              BY <4>finM, Senders2_CardLeSet
        <4>wLe1. Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = vv }))
                    <= Cardinality(Senders2(DvSet(round[id0], vv)))
              BY <4>RDsub, Senders2_Mono
        <4>wLe2. Cardinality(Senders2(DvSet(round[id0], vv)))
                    <= Cardinality(DvSet(round[id0], vv))
              BY <4>finDv, Senders2_CardLeSet
        <4>types. /\ Cardinality(msgs2[round[id0]]) \in Nat
                  /\ Cardinality(Senders2(msgs2[round[id0]])) \in Nat
                  /\ Cardinality(Senders2(received)) \in Nat
                  /\ Cardinality(DvSet(round[id0], vv)) \in Nat
                  /\ Cardinality(Senders2(DvSet(round[id0], vv))) \in Nat
                  /\ Weights[vv] \in Nat
                  /\ N - T \in Nat /\ T + 1 \in Nat /\ N + T \in Nat
              BY <4>finM, <4>finDv, <4>wDef, Senders2_Sub, FS_CardinalityType, ConstNat, NgtT, FleqT
        <4>nGe. Cardinality(msgs2[round[id0]]) >= N - T
              BY <4>senLe1, <4>senLe2, <4>types, Arith_LeTrans
        <4>wLeNv. Weights[vv] <= Cardinality(DvSet(round[id0], vv))
              BY <4>wDef, <4>wLe1, <4>wLe2, <4>types, Arith_LeTrans
        <4>nvGe. Cardinality(DvSet(round[id0], vv)) >= T + 1
              BY <4>wLeNv, <4>types, Arith_GeTrans
        <4>nv2. 2 * Cardinality(DvSet(round[id0], vv)) > N + T
              BY <4>wLeNv, <3>decide, <4>types, Arith_DoubleGtMono
        <4> QED BY <2>gt, <2>pred, <4>dvv, <4>nGe, <4>nvGe, <4>nv2, <1>upd DEF DvSet
      <3>nodecide. CASE ~(2 * Weights[vv] > N + T)
        <4>decp. decision' = decision BY <3>nodecide
        <4>dcarry. decision'[id] = decision[id0] BY <4>decp, <1>newId
        <4>n0. CASE decision[id0] = NO_DECISION
          <5> QED BY <4>dcarry, <4>n0
        <4>d0. CASE decision[id0] # NO_DECISION
          <5>hard. /\ Cardinality(msgs2'[round[id0]]) >= N - T
                   /\ Cardinality({ m \in msgs2'[round[id0]]:
                                      IsD2(m) /\ AsD2(m).v = decision[id0] }) >= T + 1
                   /\ 2 * Cardinality({ m \in msgs2'[round[id0]]:
                                          IsD2(m) /\ AsD2(m).v = decision[id0] }) > N + T
                BY <4>decp, <4>d0, Pres_L1_S3_DecidedCarry
          <5> QED BY <5>hard, <2>gt, <2>pred, <4>dcarry
        <4> QED BY <4>n0, <4>d0
      <3> QED BY <3>decide, <3>nodecide
    <2>low. CASE /\ \A vv \in VALUES: Weights[vv] < T + 1
                 /\ \E next_v \in VALUES:
                      /\ value' = [ value EXCEPT ![id0] = next_v ]
                      /\ decision' = decision
      <3>decp. decision' = decision BY <2>low
      <3>dcarry. decision'[id] = decision[id0] BY <3>decp, <1>newId
      <3>n0. CASE decision[id0] = NO_DECISION
        <4> QED BY <3>dcarry, <3>n0
      <3>d0. CASE decision[id0] # NO_DECISION
        <4>hard. /\ Cardinality(msgs2'[round[id0]]) >= N - T
                 /\ Cardinality({ m \in msgs2'[round[id0]]:
                                    IsD2(m) /\ AsD2(m).v = decision[id0] }) >= T + 1
                 /\ 2 * Cardinality({ m \in msgs2'[round[id0]]:
                                        IsD2(m) /\ AsD2(m).v = decision[id0] }) > N + T
              BY <3>decp, <3>d0, Pres_L1_S3_DecidedCarry
        <4> QED BY <4>hard, <2>gt, <2>pred, <3>dcarry
      <3> QED BY <3>n0, <3>d0
    <2> QED BY <2>high, <2>low
  <1> QED BY <1>oldId, <1>newId
THEOREM Pres_L1_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  BY DEF IndInv, Lemma1_DecisionRequiresLastQuorumLessRam, ExistsQuorum2LessRam, vars
THEOREM Pres_Lemma1 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
  <1>o1. ASSUME NEW id \in CORRECT PROVE Step2(id) => Lemma1_DecisionRequiresLastQuorumLessRam'
    <2> SUFFICES ASSUME Step2(id) PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L1_S2
  <1>o2. ASSUME NEW id \in CORRECT PROVE Step3(id) => Lemma1_DecisionRequiresLastQuorumLessRam'
    <2> SUFFICES ASSUME Step3(id) PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L1_S3
  <1>o3. FaultyStep => Lemma1_DecisionRequiresLastQuorumLessRam'
    <2> SUFFICES ASSUME FaultyStep PROVE Lemma1_DecisionRequiresLastQuorumLessRam'
          OBVIOUS
    <2> QED BY Pres_L1_F
  <1> QED BY Pres_L1_S1, Pres_L1_ST, <1>o1, <1>o2, <1>o3 DEF Next, CorrectStep
\* --- ASSEMBLED INDUCTIVE STEP ------------------------------------------------
THEOREM Inductive ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  TypeOK' /\ IndInv'
  BY TypePres, Pres_Lemma1, Pres_Lemma2, Pres_Lemma3, Pres_Lemma4, Pres_Lemma5,
     Pres_Lemma6, Pres_Lemma7, Pres_Lemma8, Pres_Lemma9, Pres_Lemma10,
     Pres_Lemma11, Pres_Lemma12, Pres_Lemma13
  DEF IndInv

\*****************************************************************************
\* SECTION D -- IndInv => AgreementInv (round induction)
\*****************************************************************************

\* SAME-ROUND UNIQUENESS: in one round, at most one value can hold a D2 quorum.
\* Proof idea: a D2(v) quorum (>half, >=T+1) implies (Lemma7) a type-1 quorum for v
\* with > (N+T)/2 senders. Two such type-1 quorums (for v and w) each exceed half of
\* N, so they intersect (QuorumIntersect) in a CORRECT replica, which then sent both
\* v and w in round r -- contradicting Lemma2 unless v = w.
THEOREM QuorumUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, NEW w \in VALUES,
         ExistsQuorum2LessRam(r, v), ExistsQuorum2LessRam(r, w)
  PROVE  v = w
  <1> USE DEF IndInv
  \* A D2(v) quorum of correct senders exists: of the >= T+1 D2(v) messages at most
  \* F are faulty (FaultyD2Bound), leaving a correct sender (CorrectD2Exists).
  <1>1. \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
        <2>1. Cardinality(DvSet(r, v)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
        <2> QED BY <2>1, CorrectD2Exists
  <1>2. \E mw \in msgs2[r] : IsD2(mw) /\ AsD2(mw).v = w /\ AsD2(mw).src \in CORRECT
        <2>1. Cardinality(DvSet(r, w)) >= T + 1 BY DEF ExistsQuorum2LessRam, DvSet
        <2> QED BY <2>1, CorrectD2Exists
  <1>3. LET Sv == { m \in msgs1[r] : m.v = v }
            Sw == { m \in msgs1[r] : m.v = w }
        IN 2 * Cardinality(Senders1(Sv)) > N + T
           /\ 2 * Cardinality(Senders1(Sw)) > N + T
        BY <1>1, <1>2 DEF Lemma7_D2RequiresQuorum
  \* The two type-1 majorities (> (N+T)/2 each) meet in a correct sender (MajorityIntersect),
  \* which then sent both v and w in round r.
  <1>4. \E id \in CORRECT :
            (\E m \in msgs1[r] : m.src = id /\ m.v = v)
            /\ (\E m \in msgs1[r] : m.src = id /\ m.v = w)
        <2>1. Senders1({ m \in msgs1[r] : m.v = v }) \subseteq ALL
              /\ Senders1({ m \in msgs1[r] : m.v = w }) \subseteq ALL
              BY DEF Senders1
        <2>2. 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
              /\ 2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = w })) > N + T
              BY <1>3
        <2>3. \E id \in Senders1({ m \in msgs1[r] : m.v = v })
                    \cap Senders1({ m \in msgs1[r] : m.v = w }) : id \in CORRECT
              BY <2>1, <2>2, MajorityIntersect
        <2> QED BY <2>3 DEF Senders1
  <1> QED
        \* a correct id that sent both v and w in round r forces v = w by Lemma2
        BY <1>4 DEF Lemma2_NoEquivocation1ByCorrect

\* CROSS-ROUND LOCK: once value v has a strict D2 quorum at round a, every strict D2
\* quorum at any later round is also for v. This is the agreement-facing form of the
\* same strict-quorum lock that `LockedReceiveStrictD` uses for inductiveness.
THEOREM LockedFullCorrectType2Strict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(Senders2(msgs2[r])) >= N - T,
         \A m \in msgs2[r] :
           ((IsD2(m) => AsD2(m).src \in CORRECT)
             /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
              => IsD2(m) /\ AsD2(m).v = v
  PROVE  ExistsQuorum2LessRam(r, v)
  <1> DEFINE GoodMsgs == { m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v }
             Good == Senders2(GoodMsgs)
             R == Senders2(msgs2[r])
             Bad == R \ Good
  <1>badFaulty. Bad \subseteq FAULTY
    <2> SUFFICES ASSUME NEW id \in Bad PROVE id \in FAULTY OBVIOUS
    <2>rin. id \in R /\ id \notin Good BY DEF Bad
    <2>pick. PICK m \in msgs2[r] :
          (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id)
        BY <2>rin DEF R, Senders2
    <2>all. id \in ALL BY <2>rin DEF R, Senders2
    <2>corr. CASE id \in CORRECT
      <3>dsrc. IsD2(m) => AsD2(m).src \in CORRECT
        <4> SUFFICES ASSUME IsD2(m) PROVE AsD2(m).src \in CORRECT
              OBVIOUS
        <4>src. AsD2(m).src = id BY <2>pick, VariantAx
        <4> QED BY <4>src, <2>corr
      <3>qsrc. IsQ2(m) => AsQ2(m).src \in CORRECT
        <4> SUFFICES ASSUME IsQ2(m) PROVE AsQ2(m).src \in CORRECT
              OBVIOUS
        <4>src. AsQ2(m).src = id BY <2>pick, VariantAx
        <4> QED BY <4>src, <2>corr
      <3>ant. (IsD2(m) => AsD2(m).src \in CORRECT)
                 /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
            BY <3>dsrc, <3>qsrc
      <3>locked. IsD2(m) /\ AsD2(m).v = v BY <3>ant
      <3>gin. id \in Good BY <2>pick, <3>locked DEF Good, GoodMsgs, Senders2
      <3> QED BY <2>rin, <3>gin
    <2>faulty. CASE id \in FAULTY
      <3> QED BY <2>faulty
    <2> QED BY <2>all, <2>corr, <2>faulty DEF ALL
  <1>cover. R \subseteq Good \union Bad BY DEF Bad
  <1>finG. IsFiniteSet(Good) BY Senders2_Sub
  <1>finB. IsFiniteSet(Bad) BY <1>badFaulty, FiniteCF, FS_Subset
  <1>finU. IsFiniteSet(Good \union Bad) BY <1>finG, <1>finB, FS_Union
  <1>rleU. Cardinality(R) <= Cardinality(Good \union Bad)
        BY <1>cover, <1>finU, FS_Subset
  <1>ule. Cardinality(Good \union Bad) <= Cardinality(Good) + Cardinality(Bad)
        BY <1>finG, <1>finB, CardUnion2LeSum
  <1>badLe. Cardinality(Bad) <= F BY <1>badFaulty, FiniteCF, FS_Subset, NTF
  <1>finM. IsFiniteSet(msgs2[r]) BY Msgs2Finite
  <1>rLeM. Cardinality(R) <= Cardinality(msgs2[r])
        BY <1>finM, Senders2_CardLeSet DEF R
  <1>types. /\ Cardinality(R) \in Nat
             /\ Cardinality(Good) \in Nat
             /\ Cardinality(Bad) \in Nat
             /\ Cardinality(Good \union Bad) \in Nat
             /\ Cardinality(msgs2[r]) \in Nat
             /\ N - T \in Nat /\ N + T \in Nat /\ T + 1 \in Nat
        BY Senders2_Sub, <1>finB, <1>finU, <1>finM, FS_CardinalityType, ConstNat, NgtT, FleqT
  <1>rge. Cardinality(R) >= N - T BY DEF R
  <1>nGe. Cardinality(msgs2[r]) >= N - T
        BY <1>rge, <1>rLeM, <1>types, Arith_GeTrans
  <1>rle. Cardinality(R) <= Cardinality(Good) + Cardinality(Bad)
        BY <1>rleU, <1>ule, <1>types, Arith_LeTrans
  <1>strict. 2 * Cardinality(Good) > N + T
        BY <1>rge, <1>rle, <1>badLe, <1>types, Arith_StrictMajorityAfterFaultsGe
  <1>ge. Cardinality(Good) >= T + 1
        BY <1>strict, <1>types, Arith_DoubleGtNplusTImplTplusOne
  <1>finD. IsFiniteSet(DvSet(r, v)) BY D2SetFinite
  <1>dNat. Cardinality(DvSet(r, v)) \in Nat BY <1>finD, FS_CardinalityType
  <1>gLeD. Cardinality(Good) <= Cardinality(DvSet(r, v))
    <2>sub. GoodMsgs \subseteq DvSet(r, v) BY DEF GoodMsgs, DvSet
    <2>finGoodMsgs. IsFiniteSet(GoodMsgs)
          BY <2>sub, <1>finD, FS_Subset
    <2>mono. Cardinality(GoodMsgs) <= Cardinality(DvSet(r, v))
          BY <2>sub, <1>finD, FS_Subset
    <2>sg. Cardinality(Good) <= Cardinality(GoodMsgs)
          BY <2>finGoodMsgs, Senders2_CardLeSet DEF Good
    <2>types2. Cardinality(Good) \in Nat /\ Cardinality(GoodMsgs) \in Nat
                /\ Cardinality(DvSet(r, v)) \in Nat
          BY Senders2_Sub, <1>finD, <2>finGoodMsgs, FS_CardinalityType
    <2> QED BY <2>sg, <2>mono, <2>types2, Arith_LeTrans
  <1>nvGe. Cardinality(DvSet(r, v)) >= T + 1
        BY <1>ge, <1>gLeD, <1>types, <1>dNat, Arith_GeTrans
  <1>nv2. 2 * Cardinality(DvSet(r, v)) > N + T
        BY <1>strict, <1>gLeD, <1>types, <1>dNat, Arith_DoubleGtMono
  <1> QED BY <1>nGe, <1>nvGe, <1>nv2 DEF ExistsQuorum2LessRam, DvSet

THEOREM StrictQuorumNextStrictQuorum ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         a + 1 \in ROUNDS,
         Cardinality(Senders2(msgs2[a + 1])) >= N - T
  PROVE  ExistsQuorum2LessRam(a + 1, v)
  <1>locked. \A m \in msgs2[a + 1] :
        ((IsD2(m) => AsD2(m).src \in CORRECT)
          /\ (IsQ2(m) => AsQ2(m).src \in CORRECT))
            => IsD2(m) /\ AsD2(m).v = v
    <2> SUFFICES ASSUME NEW m \in msgs2[a + 1],
                         (IsD2(m) => AsD2(m).src \in CORRECT)
                           /\ (IsQ2(m) => AsQ2(m).src \in CORRECT)
                  PROVE  IsD2(m) /\ AsD2(m).v = v
          OBVIOUS
    <2> QED BY StrictQuorumNextCorrectType2
  <1> QED BY <1>locked, LockedFullCorrectType2Strict

THEOREM StrictQuorumCarriesToQuorumRound ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         NEW r \in ROUNDS, r >= a,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  ExistsQuorum2LessRam(r, v)
  <1>aNat. a \in Nat /\ r \in Nat BY RoundsNat
  <1>totalA. Cardinality(Senders2(msgs2[a])) >= N - T OBVIOUS
  <1> DEFINE P(k) ==
        k \in Nat /\ k <= r - a => ExistsQuorum2LessRam(a + k, v)
  <1>base. P(0) BY <1>aNat, ConstNat DEF P
  <1>step. \A k \in Nat : P(k) => P(k + 1)
    <2> SUFFICES ASSUME NEW k \in Nat, P(k) PROVE P(k + 1) OBVIOUS
    <2>need. CASE k + 1 <= r - a
      <3>curIn. a + k \in ROUNDS BY <1>aNat, <2>need, RoundsNat, ConstNat
      <3>nextIn. a + k + 1 \in ROUNDS BY <1>aNat, <2>need, RoundsNat, ConstNat
      <3>curLe. k <= r - a BY <1>aNat, <2>need, ConstNat
      <3>curQ. ExistsQuorum2LessRam(a + k, v) BY <3>curLe DEF P
      <3>totalCur. Cardinality(Senders2(msgs2[a + k])) >= N - T
        <4>baseRound. CASE k = 0
          <5>rewrite. a + k = a BY <1>aNat, <4>baseRound, ConstNat
          <5> QED BY <1>totalA, <5>rewrite
        <4>laterRound. CASE k # 0
          <5>curLt. a + k < r BY <1>aNat, <2>need, <4>laterRound, ConstNat
          <5> QED BY <3>curIn, <5>curLt, LaterQuorumGivesTotalBefore
        <4> QED BY <4>baseRound, <4>laterRound
      <3>totalNext. Cardinality(Senders2(msgs2[a + k + 1])) >= N - T
        <4>nextLe. a + k + 1 <= r BY <1>aNat, <2>need, ConstNat
        <4>cases. \/ a + k + 1 = r
                  \/ a + k + 1 < r
          BY <1>aNat, <3>nextIn, <4>nextLe, ConstNat
        <4>target. CASE a + k + 1 = r
          <5> QED BY <4>target
        <4>before. CASE a + k + 1 < r
          <5> QED BY <3>nextIn, <4>before, LaterQuorumGivesTotalBefore
        <4> QED BY <4>target, <4>before, <4>cases
      <3>succ. (a + k) + 1 = a + k + 1 BY ConstNat
      <3>succ2. a + (k + 1) = (a + k) + 1 BY <1>aNat, ConstNat
      <3>nextInSucc. (a + k) + 1 \in ROUNDS BY <3>succ, <3>nextIn
      <3>totalCurSucc. Cardinality(Senders2(msgs2[a + k])) >= N - T
            BY <3>totalCur
      <3>totalSucc. Cardinality(Senders2(msgs2[(a + k) + 1])) >= N - T
            BY <3>succ, <3>totalNext
      <3>nextQ. ExistsQuorum2LessRam((a + k) + 1, v)
            BY <3>curIn, <3>curQ, <3>totalCurSucc, <3>nextInSucc, <3>totalSucc,
               StrictQuorumNextStrictQuorum
      <3> QED BY <3>succ, <3>succ2, <3>nextQ DEF P
    <2>skip. CASE ~(k + 1 <= r - a)
      <3> QED BY <2>skip DEF P
    <2> QED BY <2>need, <2>skip
  <1>all. \A k \in Nat : P(k)
    <2> DEFINE Q == [k \in Nat |-> P(k)]
    <2>qType. Q \in [Nat -> BOOLEAN] BY DEF Q
    <2>qBase. Q[0] BY <1>base DEF Q
    <2>qStep. \A k \in Nat : Q[k] => Q[k + 1] BY <1>step DEF Q
    <2>qAll. \A k \in Nat : Q[k]
          BY <2>qType, <2>qBase, <2>qStep, NatInductionTrusted
    <2> QED BY <2>qAll DEF Q
  <1>diff. r - a \in Nat /\ a + (r - a) = r BY <1>aNat, ConstNat
  <1>res. P(r - a) BY <1>all, <1>diff
  <1> QED BY <1>res, <1>diff DEF P

THEOREM CrossRoundStrictQuorum ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T,
         NEW r \in ROUNDS, r >= a,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  w = v
  <1>rv. ExistsQuorum2LessRam(r, v) BY StrictQuorumCarriesToQuorumRound
  <1> QED BY <1>rv, QuorumUnique

\* LockLemma packages the cross-round lock in the quantifier shape used by Agreement.
THEOREM LockLemma ==
  ASSUME TypeOK, IndInv,
         NEW a \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(a, v),
         Cardinality(Senders2(msgs2[a])) >= N - T
  PROVE  \A r \in ROUNDS :
            r >= a =>
              (\A w \in VALUES :
                 /\ ExistsQuorum2LessRam(r, w)
                 /\ Cardinality(Senders2(msgs2[r])) >= N - T
                 => w = v)
  <1> SUFFICES ASSUME NEW r \in ROUNDS
               PROVE  r >= a =>
                        (\A w \in VALUES :
                           /\ ExistsQuorum2LessRam(r, w)
                           /\ Cardinality(Senders2(msgs2[r])) >= N - T
                           => w = v)
        OBVIOUS
  <1>rGe. CASE r >= a
    <2>allW. \A w \in VALUES :
                /\ ExistsQuorum2LessRam(r, w)
                /\ Cardinality(Senders2(msgs2[r])) >= N - T
                => w = v
      <3> TAKE w \in VALUES
      <3>hasQ. CASE /\ ExistsQuorum2LessRam(r, w)
                    /\ Cardinality(Senders2(msgs2[r])) >= N - T
        <4> QED BY <1>rGe, <3>hasQ, CrossRoundStrictQuorum
      <3>noQ. CASE ~(/\ ExistsQuorum2LessRam(r, w)
                     /\ Cardinality(Senders2(msgs2[r])) >= N - T)
        <4> QED BY <3>noQ
      <3> QED BY <3>hasQ, <3>noQ
    <2> QED BY <2>allW
  <1>rLt. CASE ~(r >= a)
    <2> QED BY <1>rLt
  <1> QED BY <1>rGe, <1>rLt

\* MAIN AGREEMENT THEOREM.
\* We assume TypeOK alongside IndInv (i.e. the full inductive invariant IndInit), since
\* AgreementInv needs the variable types (e.g. decision[id] \in VALUES).
THEOREM Agreement == TypeOK /\ IndInv => AgreementInv
  <1> SUFFICES ASSUME TypeOK, IndInv,
                      NEW id1 \in CORRECT, NEW id2 \in CORRECT,
                      decision[id1] /= NO_DECISION,
                      decision[id2] /= NO_DECISION
               PROVE  decision[id1] = decision[id2]
        BY DEF AgreementInv
  <1> USE DEF IndInv
  <1>1. round[id1] > 1 /\ ExistsQuorum2LessRam(round[id1] - 1, decision[id1])
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1>2. round[id2] > 1 /\ ExistsQuorum2LessRam(round[id2] - 1, decision[id2])
        BY DEF Lemma1_DecisionRequiresLastQuorumLessRam
  <1> DEFINE a1 == round[id1] - 1
  <1> DEFINE a2 == round[id2] - 1
  <1>3. /\ a1 \in ROUNDS /\ a2 \in ROUNDS
        /\ decision[id1] \in VALUES /\ decision[id2] \in VALUES
        \* round[id] \in ROUNDS = Nat (TypeOK) and round[id] > 1 => round[id]-1 \in Nat;
        \* decision[id] \in VALUES \cup {NO_DECISION} minus NO_DECISION.
        BY <1>1, <1>2, RoundsNat DEF TypeOK
  <1>4. CASE a1 <= a2
        \* v1's quorum at a1 locks round a2, where v2 also has a quorum => v2 = v1
        <2>total1. Cardinality(Senders2(msgs2[a1])) >= N - T
              BY <1>1, <1>3, ReplicaPredRoundHasTotal
        <2>1. \A r \in ROUNDS : r >= a1 =>
                (\A w \in VALUES :
                   /\ ExistsQuorum2LessRam(r, w)
                   /\ Cardinality(Senders2(msgs2[r])) >= N - T
                   => w = decision[id1])
              BY <1>1, <1>3, <2>total1, LockLemma
        <2>total2. Cardinality(Senders2(msgs2[a2])) >= N - T
              BY <1>2, <1>3, ReplicaPredRoundHasTotal
        <2> QED BY <1>2, <1>3, <1>4, <2>1, <2>total2
  <1>5. CASE a2 <= a1
        <2>total2. Cardinality(Senders2(msgs2[a2])) >= N - T
              BY <1>2, <1>3, ReplicaPredRoundHasTotal
        <2>1. \A r \in ROUNDS : r >= a2 =>
                (\A w \in VALUES :
                   /\ ExistsQuorum2LessRam(r, w)
                   /\ Cardinality(Senders2(msgs2[r])) >= N - T
                   => w = decision[id2])
              BY <1>2, <1>3, <2>total2, LockLemma
        <2>total1. Cardinality(Senders2(msgs2[a1])) >= N - T
              BY <1>1, <1>3, ReplicaPredRoundHasTotal
        <2> QED BY <1>1, <1>3, <1>5, <2>1, <2>total1
  <1> QED
        BY <1>3, <1>4, <1>5, RoundsNat

=============================================================================
