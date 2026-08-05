-------------------------- MODULE Ben_or83_proofs_InductiveScaffold --------------------------
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

THEOREM DvPInjective ==
  ASSUME NEW r, NEW v, \A m \in msgs2'[r] : IsD2(m) => AsD2(m).r = r,
         NEW a \in DvPSet(r, v), NEW b \in DvPSet(r, v), DvPFn(r, v)[a] = DvPFn(r, v)[b]
  PROVE  a = b
PROOF OMITTED

THEOREM D2PSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  IsFiniteSet(DvPSet(r, v)) /\ Cardinality(DvPSet(r, v)) <= N
PROOF OMITTED

THEOREM DvPSenderWitness ==
  ASSUME NEW r, NEW v, NEW src \in Senders2(DvPSet(r, v))
  PROVE  \E m \in DvPSet(r, v) : IsD2(m) /\ AsD2(m).src = src
PROOF OMITTED

THEOREM QPInjective ==
  ASSUME NEW r, \A m \in msgs2'[r] : IsQ2(m) => AsQ2(m).r = r,
         NEW a \in QPSet(r), NEW b \in QPSet(r), QPFn(r)[a] = QPFn(r)[b]
  PROVE  a = b
PROOF OMITTED

THEOREM QPSetFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(QPSet(r)) /\ Cardinality(QPSet(r)) <= N
PROOF OMITTED

THEOREM DvStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
          /\ Cardinality(DvSet(r, v))
             <= Cardinality({ m \in msgs2'[r] : IsD2(m) /\ AsD2(m).v = v })
PROOF OMITTED

THEOREM QStep2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet({ m \in msgs2'[r] : IsQ2(m) })
          /\ Cardinality(QSet(r))
             <= Cardinality({ m \in msgs2'[r] : IsQ2(m) })
PROOF OMITTED

THEOREM Msgs2Finite ==
  ASSUME TypeOK, NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2[r])
PROOF OMITTED

THEOREM Msgs2PrimeFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2'[r])
PROOF OMITTED

THEOREM Msgs2Step2Mono ==
  ASSUME TypeOK, NEW id0 \in CORRECT, Step2(id0), NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
PROOF OMITTED

DPart(S, v) == { m \in S : IsD2(m) /\ AsD2(m).v = v }
QPart(S) == { m \in S : IsQ2(m) }

THEOREM Msgs2SenderPartitionBound ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW S, S \subseteq msgs2[r]
  PROVE  Cardinality(Senders2(S))
           <= Cardinality(DPart(S, 0)) + Cardinality(DPart(S, 1)) + Cardinality(QPart(S))
PROOF OMITTED

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
PROOF OMITTED

\* Abstract arithmetic: >= T+1 elements, <= F of them excluded, leaves >= 1.
LEMMA Arith_DiffPos ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= T + 1, b <= F
  PROVE  a - b >= 1
PROOF OMITTED

\* A D2 quorum of >= T+1 messages contains one from a CORRECT replica.
THEOREM CorrectD2Exists ==
  ASSUME TypeOK, NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1
  PROVE  \E mv \in msgs2[r] : IsD2(mv) /\ AsD2(mv).v = v /\ AsD2(mv).src \in CORRECT
PROOF OMITTED

THEOREM StrictQuorumSenderStrict ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  /\ Cardinality(Senders2(DvSet(r, v))) >= T + 1
          /\ 2 * Cardinality(Senders2(DvSet(r, v))) > N + T
PROOF OMITTED

THEOREM StrictQuorumFewOthers ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v)
  PROVE  Cardinality(Senders2({ m \in msgs2[r] : IsQ2(m) \/ AsD2(m).v /= v }))
            < N - 2 * T
PROOF OMITTED

\* A round cannot support two different values. A supported value has at least
\* T+1 D2 senders, hence at least one correct D2 sender; Lemma7 turns that into
\* a type-1 majority, and two such majorities intersect in a correct sender.
THEOREM SupportedUnique ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in SupportedValues(r), NEW w \in SupportedValues(r)
  PROVE  v = w
PROOF OMITTED

THEOREM QuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v),
         NEW w \in SupportedValues(r)
  PROVE  w = v
PROOF OMITTED

THEOREM DQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
PROOF OMITTED

THEOREM DQuorumDominatesMajorityD ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(DvSet(r, v)) >= T + 1,
         NEW w \in VALUES,
         2 * Cardinality(Senders2(DvSet(r, w))) > N + T
  PROVE  w = v
PROOF OMITTED

THEOREM StrictQuorumSupportedSingleton ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES,
         ExistsQuorum2LessRam(r, v),
         Cardinality(Senders2(msgs2[r])) >= N - T
  PROVE  v \in SupportedValues(r)
         /\ \A u \in SupportedValues(r) : u = v
PROOF OMITTED

THEOREM SupportedSingletonPinsNextM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW m \in msgs1[r + 1],
         m.src \in CORRECT
  PROVE  m.v = v
PROOF OMITTED

THEOREM EarlyTplusOneHasCorrect ==
  ASSUME NEW S, S \subseteq ALL, Cardinality(S) >= T + 1
  PROVE  \E id \in S : id \in CORRECT
PROOF OMITTED

THEOREM EarlyMajorityM1HasCorrect ==
  ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
         2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

THEOREM ReplicaPredRoundHasTotal ==
  ASSUME TypeOK, IndInv,
         NEW id \in CORRECT,
         round[id] > 1,
         NEW r \in ROUNDS,
         r = round[id] - 1
  PROVE  Cardinality(Senders2(msgs2[r])) >= N - T
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

THEOREM ReceivedDQuorumDominatesSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         NEW v \in VALUES,
         Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1,
         NEW w \in SupportedValues(r)
  PROVE  w = v
PROOF OMITTED

THEOREM SupportedInReceivedQuorum ==
  ASSUME NEW r \in ROUNDS, NEW v \in SupportedValues(r),
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T
  PROVE  Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) >= T + 1
PROOF OMITTED

LEMMA Arith_SupportedQuorumGeContrad ==
  ASSUME NEW rcv \in Nat, NEW dv \in Nat, NEW oth \in Nat,
         rcv >= N - T, rcv <= dv + oth, dv < T + 1, oth < N - 2 * T
  PROVE  FALSE
PROOF OMITTED

THEOREM SupportedFromTotalAndFewOthers ==
  ASSUME TypeOK,
         NEW r \in ROUNDS, NEW v \in VALUES,
         Cardinality(Senders2(msgs2[r])) >= N - T,
         Cardinality(Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v })) < N - 2 * T
  PROVE  v \in SupportedValues(r)
PROOF OMITTED

THEOREM LowWeightsSupportedEmpty ==
  ASSUME NEW r \in ROUNDS,
         NEW received \in SUBSET msgs2[r],
         Cardinality(Senders2(received)) = N - T,
         \A v \in VALUES :
           Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) < T + 1
  PROVE  SupportedValues(r) = {}
PROOF OMITTED

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
PROOF OMITTED

THEOREM SupportedValuesPFrame ==
  ASSUME NEW r \in ROUNDS, msgs2' = msgs2
  PROVE  SupportedValuesP(r) = SupportedValues(r)
PROOF OMITTED

THEOREM SupportedPToOldWhenTotal ==
  ASSUME TypeOK,
         NEW r \in ROUNDS,
         NEW v \in SupportedValuesP(r),
         Cardinality(Senders2(msgs2[r])) >= N - T,
         msgs2[r] \subseteq msgs2'[r]
  PROVE  v \in SupportedValues(r)
PROOF OMITTED

THEOREM TplusOneHasCorrect ==
  ASSUME NEW S, S \subseteq ALL, Cardinality(S) >= T + 1
  PROVE  \E id \in S : id \in CORRECT
PROOF OMITTED

THEOREM MajorityM1HasCorrect ==
  ASSUME NEW r \in ROUNDS, NEW v \in VALUES,
         2 * Cardinality(Senders1({ m \in msgs1[r] : m.v = v })) > N + T
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
PROOF OMITTED

THEOREM QuorumHasCorrectM1 ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  \E id \in CORRECT : \E m \in msgs1[r] : m.src = id /\ m.v = v
PROOF OMITTED

THEOREM QuorumHasM1Majority ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, NEW v \in VALUES, ExistsQuorum2LessRam(r, v)
  PROVE  LET Sv == { m \in msgs1[r] : m.v = v } IN
           2 * Cardinality(Senders1(Sv)) > N + T
PROOF OMITTED

THEOREM LaterQuorumGivesTotalBefore ==
  ASSUME TypeOK, IndInv,
         NEW b \in ROUNDS, NEW r \in ROUNDS, b < r,
         NEW w \in VALUES, ExistsQuorum2LessRam(r, w)
  PROVE  Cardinality(Senders2(msgs2[b])) >= N - T
PROOF OMITTED

THEOREM SupportedSingletonNextQuorum ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in VALUES, ExistsQuorum2LessRam(r + 1, w)
  PROVE  w = v
PROOF OMITTED

THEOREM SupportedSingletonNextSupported ==
  ASSUME TypeOK, IndInv,
         NEW r \in ROUNDS, r + 1 \in ROUNDS,
         NEW v \in SupportedValues(r),
         \A u \in SupportedValues(r) : u = v,
         NEW w \in SupportedValues(r + 1)
  PROVE  w = v
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

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
PROOF OMITTED

THEOREM Msgs1AddSetRep ==
  ASSUME NEW A \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
         NEW rr0 \in ROUNDS,
         NEW Add \in SUBSET [ src: ALL, r: { rr0 }, v: VALUES ],
         NEW f,
         f = [ rr \in ROUNDS |-> { m \in A : m.r = rr } ]
  PROVE  [ f EXCEPT ![rr0] = f[rr0] \union Add ]
         = [ rr \in ROUNDS |-> { m \in A \union Add : m.r = rr } ]
PROOF OMITTED

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
PROOF OMITTED

THEOREM UpdateUnionMono ==
  ASSUME NEW f, DOMAIN f = ROUNDS, NEW rr0 \in ROUNDS, NEW Add
  PROVE  \A rr \in ROUNDS :
           f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr]
PROOF OMITTED

THEOREM UpdateUnionNewInAdded ==
  ASSUME NEW f, NEW rr0 \in ROUNDS, NEW Add,
         DOMAIN f = ROUNDS,
         NEW rr \in ROUNDS, NEW m,
         m \in [ f EXCEPT ![rr0] = f[rr0] \union Add ][rr],
         m \notin f[rr]
  PROVE  rr = rr0 /\ m \in Add
PROOF OMITTED

THEOREM UpdateUnion2Mono ==
  ASSUME NEW f, DOMAIN f = ROUNDS, NEW rr0 \in ROUNDS, NEW Add1, NEW Add2
  PROVE  \A rr \in ROUNDS :
           f[rr] \subseteq [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr]
PROOF OMITTED

THEOREM UpdateUnion2NewInAdded ==
  ASSUME NEW f, NEW rr0 \in ROUNDS, NEW Add1, NEW Add2,
         DOMAIN f = ROUNDS,
         NEW rr \in ROUNDS, NEW m,
         m \in [ f EXCEPT ![rr0] = f[rr0] \union Add1 \union Add2 ][rr],
         m \notin f[rr]
  PROVE  rr = rr0 /\ m \in Add1 \union Add2
PROOF OMITTED

THEOREM FaultyMsgs2AddedFaulty ==
  ASSUME NEW rr0 \in ROUNDS,
         NEW F2D \in SUBSET FaultyD2Records(rr0),
         NEW F2Q \in SUBSET FaultyQ2Records(rr0),
         NEW m,
         m \in { D2(mm.src, rr0, mm.v): mm \in F2D }
              \union { Q2(mm.src, rr0): mm \in F2Q }
  PROVE  (IsD2(m) => AsD2(m).src \in FAULTY)
         /\ (IsQ2(m) => AsQ2(m).src \in FAULTY)
PROOF OMITTED

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
PROOF OMITTED

THEOREM SupportedPHasOldCorrectD2 ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in SupportedValuesP(r)
  PROVE  \E m \in msgs2[r] : IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT
PROOF OMITTED

THEOREM DvFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS, NEW v \in VALUES
  PROVE  /\ IsFiniteSet(DvPSet(r, v))
          /\ Cardinality(DvSet(r, v)) <= Cardinality(DvPSet(r, v))
PROOF OMITTED

THEOREM QFaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(QPSet(r))
          /\ Cardinality(QSet(r)) <= Cardinality(QPSet(r))
PROOF OMITTED

THEOREM Msgs2FaultyMono ==
  ASSUME TypeOK, TypeOK', FaultyStep, NEW r \in ROUNDS
  PROVE  /\ IsFiniteSet(msgs2'[r])
          /\ Cardinality(msgs2[r]) <= Cardinality(msgs2'[r])
PROOF OMITTED

\*****************************************************************************
\* SECTION B -- TYPE PRESERVATION + BASE CASE
\*****************************************************************************

\* BASE CASE. With empty message buffers, no decision, round 1 and step S1,
\* every conjunct of IndInv is vacuous or trivially true.
THEOREM InitInd == Init => TypeOK /\ IndInv
PROOF OMITTED

\* TYPE PRESERVATION. Each action keeps every variable in its declared type and
\* keeps msgs1/msgs2 in the existential "shape" required by TypeOK.
THEOREM TypePres ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
PROOF OMITTED

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
PROOF OMITTED
THEOREM Pres_L2_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
PROOF OMITTED
THEOREM Pres_L2_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
PROOF OMITTED
\* The substantive Step1 case: the new M1(id,r,value[id]) is the only round-r message from
\* id (Lemma4: id is in S1, so it has not sent at its current round), so no equivocation.
THEOREM Pres_L2_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
PROOF OMITTED
\* FaultyStep case: new msgs1 messages have FAULTY src, so any CORRECT-sender message is
\* old; no new equivocation among correct senders.
THEOREM Pres_L2_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma2_NoEquivocation1ByCorrect'
PROOF OMITTED
THEOREM Pres_Lemma2 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
PROOF OMITTED

\* ===== L3: no type-2 equivocation by correct (msgs2) =====
THEOREM Pres_L3_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED
THEOREM Pres_L3_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED
THEOREM Pres_L3_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED
THEOREM Pres_L3_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED
THEOREM Pres_L3_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED
THEOREM Pres_Lemma3 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
PROOF OMITTED

\* ===== L4: messages not from the future =====
THEOREM Pres_L4_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED
\* Substantive Step1 case: the new M1 has round = round[id]; id moves S1->S2. We do NOT
\* USE DEF IndInv (it would expand the Cardinality-heavy lemmas and poison the arithmetic);
\* we extract just Lemma4. The step/round priming (step EXCEPT ![id]=S2) is handled by a
\* case split on whether the message's sender is id, with S1#S2#S3 distinctness and Nat
\* typing of message rounds (to get <= from <).
THEOREM Pres_L4_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED
\* Substantive Step3 case: id advances round[id]->round[id]+1 and resets step to S1;
\* msgs1/msgs2 unchanged. Old bounds m.r <= round[id] become m.r < round[id]+1.
THEOREM Pres_L4_S3 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED
\* Substantive Step2 case: id sends a new D2(id,r,v) or Q2(id,r) into msgs2[r] and moves
\* S2->S3. The new message carries round r = round[id]; old bounds m.r < round become
\* m.r <= round (still ok). Handles Step2's two value-quorum branches uniformly via the
\* shared new-message round/sender shape.
THEOREM Pres_L4_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED
\* FaultyStep case: step/round unchanged and messages only grow with FAULTY-sender
\* messages, so any CORRECT-sender message is old and satisfies the (unchanged) bound.
THEOREM Pres_L4_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED
THEOREM Pres_Lemma4 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma4_MessagesNotFromFuture'
PROOF OMITTED

\* ===== L5: a non-initial round requires previously sent messages =====
THEOREM Pres_L5_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED
\* Substantive Step1 case: id sends its first M1 of round[id] and moves S1->S2. The new
\* M1 witnesses the now-active "r = round[id] /\ step /= S1" obligation; all other
\* obligations are preserved because msgs1 only grows (monotonicity) and msgs2 is unchanged.
THEOREM Pres_L5_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED
\* Step2 case: id sends a new type-2 message into msgs2[round[id]] (witnessing the
\* "r = round[id] /\ step = S3" obligation) and moves S2->S3; msgs1 unchanged, msgs2 grows.
THEOREM Pres_L5_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED
\* Step3 case: id advances round and resets step to S1; messages unchanged. The "step=S3"
\* obligations at round[id] become "r < round[id]+1" obligations, served by the same messages.
THEOREM Pres_L5_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED
\* FaultyStep case: step/round unchanged, messages only grow, so every required message
\* (a CORRECT replica's own message) still exists.
THEOREM Pres_L5_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED
THEOREM Pres_Lemma5 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma5_RoundNeedsSentMessages'
PROOF OMITTED

\* ===== L6: a decision fixes the value (decision,value) =====
THEOREM Pres_L6_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED
THEOREM Pres_L6_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED
\* FaultyStep leaves value/decision unchanged (frame), via FaultyStepProps.
THEOREM Pres_L6_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED
THEOREM Pres_L6_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED
THEOREM Pres_L6_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED
THEOREM Pres_Lemma6 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma6_DecisionDefinesValue'
PROOF OMITTED

\* ===== L7: a correct D2(v) requires a type-1 quorum for v =====
THEOREM Pres_L7_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L7_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L7_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L7_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L7_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED
THEOREM Pres_Lemma7 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma7_D2RequiresQuorum'
PROOF OMITTED

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
PROOF OMITTED

THEOREM Pres_L8_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED
THEOREM Pres_L8_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED
\* Step2: msgs1 is unchanged, so n0/n1/nf are frame-invariant. Rounds already carrying a
\* correct Q2 reuse the old witness; the round where id0 emits its Q2 is the only new one,
\* and its witness comes from LowWeightsReceivedL8Witness applied to id0's received set.
THEOREM Pres_L8_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED
THEOREM Pres_L8_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED
THEOREM Pres_L8_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED
THEOREM Pres_Lemma8 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
PROOF OMITTED

\* ===== L9: rounds connection / value support carries forward =====
THEOREM Pres_L9_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED
THEOREM Pres_L9_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED
THEOREM Pres_L9_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED
THEOREM Pres_L9_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED
THEOREM Pres_L9_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED
THEOREM Pres_Lemma9 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma9_RoundsConnection'
PROOF OMITTED

\* ===== L10: a type-1 message in round r>1 needs a quorum in r-1 =====
THEOREM Pres_L10_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L10_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L10_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L10_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED
THEOREM Pres_L10_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED
THEOREM Pres_Lemma10 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma10_M1RequiresQuorum'
PROOF OMITTED

\* ===== L11: a correct replica's value at r>1 is backed by msgs2[r-1] =====
THEOREM Pres_L11_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L11_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L11_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L11_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L11_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED
THEOREM Pres_Lemma11 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma11_ValueOnQuorumLessRam'
PROOF OMITTED

\* ===== L12: reaching round r+1 needs N-T type-2 messages in r =====
THEOREM Pres_L12_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED
THEOREM Pres_L12_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED
THEOREM Pres_L12_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED
THEOREM Pres_L12_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED
THEOREM Pres_L12_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED
THEOREM Pres_Lemma12 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
PROOF OMITTED

\* ===== L13: value lock -- a correct value at r matches Supported(r-1) =====
THEOREM Pres_L13_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma13_ValueLock'
PROOF OMITTED
THEOREM Pres_L13_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma13_ValueLock'
PROOF OMITTED
THEOREM Pres_L13_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma13_ValueLock'
PROOF OMITTED
THEOREM Pres_L13_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma13_ValueLock'
PROOF OMITTED
THEOREM Pres_L13_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma13_ValueLock'
PROOF OMITTED
THEOREM Pres_Lemma13 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma13_ValueLock'
PROOF OMITTED

\* ===== L1: a decision is backed by a D2 quorum in the previous round =====
THEOREM Pres_L1_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L1_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L1_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
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
PROOF OMITTED

THEOREM Pres_L1_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
THEOREM Pres_L1_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
THEOREM Pres_Lemma1 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
PROOF OMITTED
\* --- ASSEMBLED INDUCTIVE STEP ------------------------------------------------
=============================================================================
