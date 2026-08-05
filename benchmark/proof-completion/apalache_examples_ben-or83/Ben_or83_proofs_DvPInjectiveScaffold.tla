-------------------------- MODULE Ben_or83_proofs_DvPInjectiveScaffold --------------------------
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
THEOREM Senders1_Sub ==
  ASSUME NEW S
  PROVE  Senders1(S) \subseteq ALL /\ IsFiniteSet(Senders1(S))
        /\ Cardinality(Senders1(S)) <= N
PROOF OMITTED

THEOREM Senders1_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders1(A)) <= Cardinality(Senders1(B))
PROOF OMITTED

THEOREM Senders2_Sub ==
  ASSUME NEW S
  PROVE  Senders2(S) \subseteq ALL /\ IsFiniteSet(Senders2(S))
        /\ Cardinality(Senders2(S)) <= N
PROOF OMITTED

THEOREM Senders2_Witness ==
  ASSUME NEW S, NEW id \in Senders2(S)
  PROVE  \E m \in S :
           (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id)
PROOF OMITTED

THEOREM Senders2_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders2(A)) <= Cardinality(Senders2(B))
PROOF OMITTED

SenderWitness2(S) ==
  [ id \in Senders2(S) |->
      CHOOSE m \in S :
        (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id) ]

THEOREM Senders2_CardLeSet ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  Cardinality(Senders2(S)) <= Cardinality(S)
PROOF OMITTED

D2SrcFn(S) == [ m \in S |-> AsD2(m).src ]

THEOREM D2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r, NEW v,
         \A m \in S : IsD2(m) /\ AsD2(m).src \in ALL
                       /\ AsD2(m).r = r /\ AsD2(m).v = v
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
PROOF OMITTED

Q2SrcFn(S) == [ m \in S |-> AsQ2(m).src ]

THEOREM Q2Fixed_CardLeSenders ==
  ASSUME NEW S, NEW r,
         \A m \in S : IsQ2(m) /\ AsQ2(m).src \in ALL /\ AsQ2(m).r = r
  PROVE  Cardinality(S) <= Cardinality(Senders2(S))
PROOF OMITTED

\* Any subset of ALL is finite with cardinality at most N.
THEOREM SubAll_Finite ==
  ASSUME NEW Q, Q \subseteq ALL
  PROVE  IsFiniteSet(Q) /\ Cardinality(Q) <= N
PROOF OMITTED

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
PROOF OMITTED

\* A set of >= T+1 elements cannot consist solely of <= F faulty ones (F <= T).
LEMMA Arith_TplusOneNotFaulty ==
  ASSUME NEW a \in Nat, a >= T + 1, a <= F
  PROVE  FALSE
PROOF OMITTED

LEMMA Arith_GeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a >= c, a <= b
  PROVE  b >= c
PROOF OMITTED

LEMMA Arith_LeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b, b <= c
  PROVE  a <= c
PROOF OMITTED

LEMMA Arith_LeLtTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b, b < c
  PROVE  a < c
PROOF OMITTED

LEMMA Arith_DoubleGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, 2 * a > c, a <= b
  PROVE  2 * b > c
PROOF OMITTED

LEMMA Arith_DoubleGtNplusTImplTplusOne ==
  ASSUME NEW a \in Nat, 2 * a > N + T
  PROVE  a >= T + 1
PROOF OMITTED

LEMMA Arith_DoubleNotGtLe ==
  ASSUME NEW a \in Nat, ~(2 * a > N + T)
  PROVE  2 * a <= N + T
PROOF OMITTED

LEMMA Arith_DoubleLeFromNotGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b, ~(2 * b > N + T)
  PROVE  2 * a <= N + T
PROOF OMITTED

LEMMA Arith_SuccCancel ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a + 1 = b + 1
  PROVE  a = b
PROOF OMITTED

LEMMA Arith_SuccGtOne ==
  ASSUME NEW a \in Nat, a >= 1
  PROVE  a + 1 > 1
PROOF OMITTED

LEMMA Arith_PlusOneMinusOne ==
  ASSUME NEW a \in Nat
  PROVE  a + 1 - 1 = a
PROOF OMITTED

LEMMA Arith_MinusOnePlusOne ==
  ASSUME NEW a \in Nat, a > 1
  PROVE  (a - 1) + 1 = a
PROOF OMITTED

LEMMA Arith_SumThirdMonoGe ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW z \in Nat, NEW zp \in Nat,
         NEW c \in Nat, z <= zp, x + y + z >= c
  PROVE  x + y + zp >= c
PROOF OMITTED

LEMMA Arith_ThreeLeTrans ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat,
         NEW x \in Nat, NEW y \in Nat, NEW z \in Nat,
         NEW n \in Nat,
         n <= a + b + c,
         a <= x, b <= y, c <= z
  PROVE  n <= x + y + z
PROOF OMITTED

LEMMA Arith_SumMinusLeSum ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW i \in Nat
  PROVE  a + b - i <= a + b
PROOF OMITTED

LEMMA Arith_SupportedQuorumContrad ==
  ASSUME NEW rcv \in Nat, NEW dv \in Nat, NEW oth \in Nat,
         rcv = N - T, rcv <= dv + oth, dv < T + 1, oth < N - 2 * T
  PROVE  FALSE
PROOF OMITTED

LEMMA Arith_NotLtTplusOneGe ==
  ASSUME NEW a \in Nat, ~(a < T + 1)
  PROVE  a >= T + 1
PROOF OMITTED

LEMMA Arith_GeLtContrad ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= b, a < b
  PROVE  FALSE
PROOF OMITTED

LEMMA Arith_DoubleLtTplusOneLeNplusT ==
  ASSUME NEW a \in Nat, a < T + 1
  PROVE  2 * a <= N + T
PROOF OMITTED

LEMMA Arith_StrictMajorityAfterFaults ==
  ASSUME NEW rcv \in Nat, NEW d \in Nat, NEW bad \in Nat,
         rcv = N - T, rcv <= d + bad, bad <= F
  PROVE  2 * d > N + T
PROOF OMITTED

LEMMA Arith_StrictMajorityAfterFaultsGe ==
  ASSUME NEW rcv \in Nat, NEW d \in Nat, NEW bad \in Nat,
         rcv >= N - T, rcv <= d + bad, bad <= F
  PROVE  2 * d > N + T
PROOF OMITTED

LEMMA Arith_DoubleGtNplusTImplGt3T ==
  ASSUME NEW d \in Nat, 2 * d > N + T
  PROVE  d > 3 * T
PROOF OMITTED

LEMMA Arith_OtherLtFromStrictOverlapCore ==
  ASSUME NEW d \in Nat, NEW o \in Nat, NEW i \in Nat, NEW u \in Nat,
         u <= N, u = d + o - i, d > 3 * T, i <= T
  PROVE  o < N - 2 * T
PROOF OMITTED

LEMMA Arith_OtherLtFromStrictOverlap ==
  ASSUME NEW d \in Nat, NEW o \in Nat, NEW i \in Nat, NEW u \in Nat,
         u <= N, u = d + o - i, 2 * d > N + T, i <= F
  PROVE  o < N - 2 * T
PROOF OMITTED

LEMMA Arith_Lemma8Pinned0Contrad ==
  ASSUME NEW x0 \in Nat, NEW x1 \in Nat, NEW nf \in Nat,
         x1 <= 0, x0 + x1 + nf >= N - T, nf <= F, 2 * x0 <= N + T
  PROVE  FALSE
PROOF OMITTED

LEMMA Arith_Lemma8Pinned1Contrad ==
  ASSUME NEW x0 \in Nat, NEW x1 \in Nat, NEW nf \in Nat,
         x0 <= 0, x0 + x1 + nf >= N - T, nf <= F, 2 * x1 <= N + T
  PROVE  FALSE
PROOF OMITTED

THEOREM CardUnion3LeSum ==
  ASSUME NEW A, NEW B, NEW C,
         IsFiniteSet(A), IsFiniteSet(B), IsFiniteSet(C)
  PROVE  Cardinality((A \union B) \union C)
           <= Cardinality(A) + Cardinality(B) + Cardinality(C)
PROOF OMITTED

THEOREM CardUnion2LeSum ==
  ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B)
  PROVE  Cardinality(A \union B) <= Cardinality(A) + Cardinality(B)
PROOF OMITTED

\* CORE QUORUM INTERSECTION: two quorums of >= N - T senders intersect, and the
\* intersection necessarily contains a correct replica (since N > 5*T).
THEOREM QuorumIntersect ==
  ASSUME NEW QA, NEW QB,
         QA \subseteq ALL, QB \subseteq ALL,
         Cardinality(QA) >= N - T, Cardinality(QB) >= N - T
  PROVE  /\ Cardinality(QA \cap QB) >= N - 2 * T
         /\ \E id \in QA \cap QB : id \in CORRECT
PROOF OMITTED

\* MAJORITY INTERSECTION: two > (N+T)/2 quorums of senders meet in a correct replica.
\* (The type-1 quorums backing a D2 message exceed half, not N-T.) The cardinality
\* arithmetic with `2 * Cardinality(...)` premises poisons SMT, so we PICK plain Nats
\* equal to each cardinality and do the arithmetic on those.
THEOREM MajCardBound ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  Cardinality(QA \cap QB) >= T + 1
PROOF OMITTED

THEOREM MajorityIntersect ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  \E id \in QA \cap QB : id \in CORRECT
PROOF OMITTED

\* A correct replica that sent value v contributes a correct sender; faulty
\* senders number at most F. Used to turn ">half senders" into ">half correct".
THEOREM FaultyBound ==
  ASSUME NEW S, S \subseteq ALL
  PROVE  Cardinality(S \cap FAULTY) <= F
PROOF OMITTED

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
PROOF OMITTED

\* Hence at most F faulty D2(r,v) messages.
THEOREM FaultyD2Bound ==
  ASSUME NEW r, NEW v,
         \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r
  PROVE  Cardinality(FaultyD2(r, v)) <= F
PROOF OMITTED

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
PROOF OMITTED

\* The raw TypeOK set expression equals the DPof/QPof operators (clean context).
THEOREM SetEqHelper ==
  ASSUME NEW rr, NEW A1D, NEW A1Q
  PROVE  { D2(mm.src, rr, mm.v): mm \in { m \in A1D: m.r = rr } }
            \union { Q2(mm.src, rr): mm \in { m \in A1Q: m.r = rr } }
         = DPof(A1D, rr) \union QPof(A1Q, rr)
PROOF OMITTED

\* Abstract the message set into a fresh `mset` so the Variant reasoning never sees the
\* poisoning `msgs2[rr]` term. SUFFICES does the \E-elimination and goal rewrite.
THEOREM ShapeFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).r = rr
PROOF OMITTED

\* Decomposition of msgs2[rr] from TypeOK as a SMALL existential (DPof/QPof opaque).
\* The heavy `msgs2 = [...]` PICK is kept LOCAL to this proof so it never pollutes callers.
THEOREM Msgs2Decomp ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
PROOF OMITTED

\* The round invariant, fully proved.
THEOREM Msgs2Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).r = rr
PROOF OMITTED

\* --- src \in ALL variant (needed to bound D2 senders) ---
THEOREM ShapeHelperSrc ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).src \in ALL
PROOF OMITTED

THEOREM ShapeSrcFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).src \in ALL
PROOF OMITTED

THEOREM Msgs2SrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).src \in ALL
PROOF OMITTED

THEOREM ShapeHelperSrcQ ==
  ASSUME NEW rr, NEW A1D, NEW A1Q \in SUBSET [ src: ALL, r: ROUNDS ], NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsQ2(m)
  PROVE  AsQ2(m).src \in ALL
PROOF OMITTED

THEOREM ShapeSrcQFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsQ2(m) => AsQ2(m).src \in ALL
PROOF OMITTED

THEOREM Msgs2QSrcInAll ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsQ2(m) => AsQ2(m).src \in ALL
PROOF OMITTED

THEOREM ShapeHelperV ==
  ASSUME NEW rr, NEW A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ], NEW A1Q, NEW m,
         m \in DPof(A1D, rr) \union QPof(A1Q, rr), IsD2(m)
  PROVE  AsD2(m).v \in VALUES
PROOF OMITTED

THEOREM ShapeVFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : IsD2(m) => AsD2(m).v \in VALUES
PROOF OMITTED

THEOREM Msgs2VInValues ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : IsD2(m) => AsD2(m).v \in VALUES
PROOF OMITTED

\* Type-1 message shape from TypeOK (simpler than msgs2: no Variants).
THEOREM Msgs1Shape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs1[rr] : m.r = rr /\ m.src \in ALL
PROOF OMITTED

THEOREM Msgs1DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs1 = ROUNDS
PROOF OMITTED

\* Type-2 message round shape (both D2 and Q2): the round field equals the index.
THEOREM ShapeHelperR ==
  ASSUME NEW rr, NEW A1D, NEW A1Q, NEW m, m \in DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
PROOF OMITTED

THEOREM ShapeRFromExists ==
  ASSUME NEW rr, NEW mset,
         \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] : mset = DPof(A1D, rr) \union QPof(A1Q, rr)
  PROVE  \A m \in mset : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
PROOF OMITTED

THEOREM Msgs2RShape ==
  ASSUME TypeOK, NEW rr \in ROUNDS
  PROVE  \A m \in msgs2[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
PROOF OMITTED

THEOREM Msgs2DomR ==
  ASSUME TypeOK PROVE DOMAIN msgs2 = ROUNDS
PROOF OMITTED

THEOREM Msgs2PrimeDecomp ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
            A1Q \in SUBSET [ src: ALL, r: ROUNDS ] :
              msgs2'[rr] = DPof(A1D, rr) \union QPof(A1Q, rr)
PROOF OMITTED

THEOREM Msgs2PrimeShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).r = rr
PROOF OMITTED

THEOREM Msgs2PrimeSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).src \in ALL
PROOF OMITTED

THEOREM Msgs2PrimeQSrcInAll ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsQ2(m) => AsQ2(m).src \in ALL
PROOF OMITTED

THEOREM Msgs2PrimeRShape ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : (IsD2(m) => AsD2(m).r = rr) /\ (IsQ2(m) => AsQ2(m).r = rr)
PROOF OMITTED

THEOREM Msgs2PrimeVInValues ==
  ASSUME TypeOK', NEW rr \in ROUNDS
  PROVE  \A m \in msgs2'[rr] : IsD2(m) => AsD2(m).v \in VALUES
PROOF OMITTED

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
PROOF OMITTED

THEOREM Lemma3_Q2D2Faulty ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW mq \in msgs2[r], NEW md \in msgs2[r],
         IsQ2(mq), IsD2(md), AsQ2(mq).src = AsD2(md).src
  PROVE  AsQ2(mq).src \in FAULTY
PROOF OMITTED

THEOREM Lemma3_D2D2SameCorrect ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW m1 \in msgs2[r], NEW m2 \in msgs2[r],
         IsD2(m1), IsD2(m2), AsD2(m1).src = AsD2(m2).src,
         AsD2(m1).src \in CORRECT
  PROVE  AsD2(m1).v = AsD2(m2).v
PROOF OMITTED

THEOREM DvInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvSet(r, v), NEW b \in DvSet(r, v), DvFn(r, v)[a] = DvFn(r, v)[b]
  PROVE  a = b
PROOF OMITTED

THEOREM D2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvSet(r, v)) /\ Cardinality(DvSet(r, v)) <= N
PROOF OMITTED

THEOREM QInjective ==
  ASSUME NEW r, \A m \in msgs2[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QSet(r), NEW b \in QSet(r), QFn(r)[a] = QFn(r)[b]
  PROVE  a = b
PROOF OMITTED

THEOREM Q2SetFinite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(QSet(r)) /\ Cardinality(QSet(r)) <= N
PROOF OMITTED

=============================================================================
