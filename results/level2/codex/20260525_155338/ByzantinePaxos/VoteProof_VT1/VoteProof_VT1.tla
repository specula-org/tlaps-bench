----------------------------- MODULE VoteProof_VT1 ------------------------------

EXTENDS Integers , FiniteSets, TLC, TLAPS

-----------------------------------------------------------------------------
CONSTANT Value,     
         Acceptor,  
         Quorum     

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
-----------------------------------------------------------------------------

Ballot == Nat
-----------------------------------------------------------------------------

VARIABLES votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

-----------------------------------------------------------------------------

NI == INSTANCE NaturalsInduction

THEOREM RecursiveFcnOfNat ==
  ASSUME NEW Def(_,_),
         ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i]
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n \in Nat] == Def(f, n)
         IN  f = [n \in Nat |-> Def(f, n)]
PROOF
  BY NI!RecursiveFcnOfNat

THEOREM NatInduction ==
  ASSUME NEW P(_),
         P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)
PROOF
  <1> DEFINE f == [n \in Nat |-> P(n)]
  <1>1. f[0]
    BY DEF f
  <1>2. \A n \in Nat : f[n] => f[n+1]
    BY DEF f
  <1>3. \A n \in Nat : f[n]
    BY <1>1, <1>2, SimpleNatInduction
  <1>4. QED
    BY <1>3 DEF f

SafeAtDef(F, bb, v) ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ F[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)

SafeAtBody(b, v) ==
        \/ b = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq b
             /\ \E c \in -1..(b-1) :
                  /\ (c # -1) => /\ SafeAt(c, v)
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)

SafeAtF(v) == CHOOSE F : F = [bb \in Ballot |-> SafeAtDef(F, bb, v)]

LEMMA SafeAtIsF == \A b, v : SafeAt(b, v) = SafeAtF(v)[b]
  PROOF BY DEF SafeAt, SafeAtF, SafeAtDef

LEMMA SafeAtDefExt ==
  \A v \in Value, n \in Nat :
    \A g, h :
      (\A i \in 0..(n-1) : g[i] = h[i])
      => SafeAtDef(g, n, v) = SafeAtDef(h, n, v)
  PROOF BY DEF SafeAtDef, VotedFor, DidNotVoteIn, Ballot

LEMMA SafeAtFRec ==
  \A v \in Value :
    SafeAtF(v) = [bb \in Ballot |-> SafeAtDef(SafeAtF(v), bb, v)]
  PROOF
  <1>1. ASSUME NEW v \in Value
        PROVE  SafeAtF(v) = [bb \in Ballot |-> SafeAtDef(SafeAtF(v), bb, v)]
    <2>. DEFINE Def(F, n) == SafeAtDef(F, n, v)
    <2>1. ASSUME NEW n \in Nat, NEW g, NEW h,
                   \A i \in 0..(n-1) : g[i] = h[i]
          PROVE  Def(g, n) = Def(h, n)
      BY <1>1, <2>1, SafeAtDefExt DEF Def
    <2>. HIDE DEF Def
    <2>2. LET f[n \in Nat] == Def(f, n)
           IN  f = [n \in Nat |-> Def(f, n)]
      BY <2>1, RecursiveFcnOfNat, Isa
    <2>3. QED
      BY <2>2 DEF Def, SafeAtF, Ballot
  <1>2. QED
    BY <1>1

LEMMA SafeAtDefBody ==
  \A b, v : SafeAtDef(SafeAtF(v), b, v) = SafeAtBody(b, v)
  PROOF BY SafeAtIsF DEF SafeAtDef, SafeAtBody

THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
  PROOF
  <1>1. ASSUME NEW b \in Ballot, NEW v \in Value
        PROVE  SafeAt(b, v) = SafeAtBody(b, v)
    <2>1. SafeAt(b, v) = SafeAtF(v)[b]
      BY SafeAtIsF
    <2>2. SafeAtF(v)[b] = SafeAtDef(SafeAtF(v), b, v)
      BY <1>1, SafeAtFRec DEF Ballot
    <2>3. SafeAtDef(SafeAtF(v), b, v) = SafeAtBody(b, v)
      BY SafeAtDefBody
    <2>4. QED
      BY <2>1, <2>2, <2>3
  <1>2. QED
    BY <1>1 DEF SafeAtBody

LEMMA SafeAtPropBody ==
  \A b \in Ballot, v \in Value : SafeAt(b, v) = SafeAtBody(b, v)
  PROOF BY SafeAtProp DEF SafeAtBody

-----------------------------------------------------------------------------

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  PROOF BY QA

LEMMA VoteOrNoVote ==
  \A a, b :
    \A v \in Value :
      (\A w \in Value : VotedFor(a, b, w) => (w = v))
      => DidNotVoteIn(a, b) \/ VotedFor(a, b, v)
  PROOF BY DEF DidNotVoteIn

SafeLemmaProp(b) ==
  \A v \in Value :
    SafeAt(b, v) =>
      \A c \in 0..(b-1) :
        \E Q \in Quorum :
          \A a \in Q : \/ DidNotVoteIn(a, c)
                       \/ VotedFor(a, c, v)

THEOREM GeneralNatInduction ==
  ASSUME NEW P(_),
         \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
  PROVE  \A n \in Nat : P(n)
PROOF
  <1> DEFINE Q(n) == \A m \in 0..n : P(m)
  <1>1. Q(0)
    OBVIOUS
  <1>2. \A n \in Nat : Q(n) => Q(n+1)
    OBVIOUS
  <1>3. \A n \in Nat : Q(n)
    BY <1>1, <1>2, NatInduction, Isa
  <1>4. QED
    BY <1>3

LEMMA SafeLemma ==
  TypeOK =>
    \A b \in Ballot : SafeLemmaProp(b)
PROOF
  <1>1. ASSUME TypeOK
        PROVE  \A b \in Ballot : SafeLemmaProp(b)
    <2>1. \A b \in Nat :
             (\A m \in 0..(b-1) : SafeLemmaProp(m)) => SafeLemmaProp(b)
      <3>1. ASSUME NEW b \in Nat,
                    \A m \in 0..(b-1) : SafeLemmaProp(m)
            PROVE  SafeLemmaProp(b)
        <4>1. ASSUME NEW v \in Value,
                      SafeAt(b, v)
              PROVE  \A c \in 0..(b-1) :
                       \E Q \in Quorum :
                         \A a \in Q : \/ DidNotVoteIn(a, c)
                                      \/ VotedFor(a, c, v)
          <5>1. ASSUME NEW c \in 0..(b-1)
                PROVE  \E Q \in Quorum :
                         \A a \in Q : \/ DidNotVoteIn(a, c)
                                      \/ VotedFor(a, c, v)
            <6>1. SafeAt(b, v) = SafeAtBody(b, v)
              BY <3>1, <4>1, SafeAtPropBody DEF Ballot
            <6>1a. SafeAtBody(b, v)
              BY <4>1, <6>1
            <6>2. CASE b = 0
              BY <5>1, <6>2
            <6>3. CASE b # 0
              <7>1. \E Q \in Quorum :
                       /\ \A a \in Q : maxBal[a] \geq b
                       /\ \E k \in -1..(b-1) :
                            /\ (k # -1) => /\ SafeAt(k, v)
                                           /\ \A a \in Q :
                                                \A w \in Value :
                                                   VotedFor(a, k, w) => (w = v)
                            /\ \A d \in (k+1)..(b-1), a \in Q :
                                 DidNotVoteIn(a, d)
                BY <6>1a, <6>3 DEF SafeAtBody
              <7>2. PICK Q \in Quorum :
                       /\ \A a \in Q : maxBal[a] \geq b
                       /\ \E k \in -1..(b-1) :
                            /\ (k # -1) => /\ SafeAt(k, v)
                                           /\ \A a \in Q :
                                                \A w \in Value :
                                                   VotedFor(a, k, w) => (w = v)
                            /\ \A d \in (k+1)..(b-1), a \in Q :
                                 DidNotVoteIn(a, d)
                BY <7>1
              <7>3. PICK k \in -1..(b-1) :
                       /\ (k # -1) => /\ SafeAt(k, v)
                                      /\ \A a \in Q :
                                           \A w \in Value :
                                              VotedFor(a, k, w) => (w = v)
                       /\ \A d \in (k+1)..(b-1), a \in Q :
                            DidNotVoteIn(a, d)
                BY <7>2
              <7>4. CASE c \in (k+1)..(b-1)
                <8>1. \A a \in Q : DidNotVoteIn(a, c)
                  BY <7>3, <7>4
                <8>2. QED
                  BY <7>2, <8>1
              <7>5. CASE c = k
                <8>1. k # -1
                  BY <5>1, <7>5
                <8>2. \A a \in Q :
                         \A w \in Value : VotedFor(a, c, w) => (w = v)
                  BY <7>3, <7>5, <8>1
                <8>3. \A a \in Q :
                         \/ DidNotVoteIn(a, c)
                         \/ VotedFor(a, c, v)
                  BY <4>1, <8>2, VoteOrNoVote
                <8>4. QED
                  BY <7>2, <8>3
              <7>6. CASE c \in 0..(k-1)
                <8>1. k \in 0..(b-1)
                  BY <7>3, <7>6
                <8>2. SafeAt(k, v)
                  BY <7>3, <8>1
                <8>3. \E Q \in Quorum :
                         \A a \in Q : \/ DidNotVoteIn(a, c)
                                      \/ VotedFor(a, c, v)
                  BY <3>1, <4>1, <7>6, <8>1, <8>2 DEF SafeLemmaProp
                <8>4. QED
                  BY <8>3
              <7>7. QED
                BY <5>1, <7>3, <7>4, <7>5, <7>6
            <6>4. QED
              BY <6>2, <6>3
          <5>2. QED
            BY <5>1
        <4>2. QED
          BY <4>1 DEF SafeLemmaProp
      <3>2. QED
        BY <3>1
    <2> DEFINE P(n) == SafeLemmaProp(n)
    <2>2. \A b \in Nat : (\A m \in 0..(b-1) : P(m)) => P(b)
      BY <2>1 DEF P
    <2>3. \A b \in Nat : P(b)
      <3> DEFINE Q(n) == \A m \in 0..n : P(m)
      <3>1. Q(0)
        BY <2>2 DEF Q
      <3>2. \A n \in Nat : Q(n) => Q(n+1)
        BY <2>2 DEF Q
      <3>3. \A n \in Nat : Q(n)
        BY <3>1, <3>2, NatInduction, Isa
      <3>4. QED
        BY <3>3 DEF Q
    <2>4. QED
      BY <2>3 DEF P, Ballot
  <1>2. QED
    BY <1>1

LEMMA OneAcceptorValue ==
  VInv1 =>
    \A a \in Acceptor, b \in Ballot, v, w \in Value :
      VotedFor(a, b, w) /\ (DidNotVoteIn(a, b) \/ VotedFor(a, b, v))
      => v = w
  PROOF BY DEF VInv1, DidNotVoteIn

LEMMA VT0 ==
  /\ TypeOK
  /\ VInv1
  /\ VInv2
  => \A v, w \in Value, b, c \in Ballot :
       (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
PROOF
  <1>1. ASSUME TypeOK, VInv1, VInv2
        PROVE  \A v, w \in Value, b, c \in Ballot :
                 (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
    <2>1. ASSUME NEW v \in Value, NEW w \in Value,
                  NEW b \in Ballot, NEW c \in Ballot,
                  b > c,
                  SafeAt(b, v),
                  ChosenIn(c, w)
          PROVE  v = w
      <3>1. c \in 0..(b-1)
        BY <2>1, SMT DEF Ballot
      <3>2. SafeLemmaProp(b)
        BY <1>1, <2>1, SafeLemma
      <3>3. \E Q \in Quorum :
               \A a \in Q : \/ DidNotVoteIn(a, c)
                            \/ VotedFor(a, c, v)
        BY <2>1, <3>1, <3>2 DEF SafeLemmaProp
      <3>4. PICK Q \in Quorum :
               \A a \in Q : \/ DidNotVoteIn(a, c)
                            \/ VotedFor(a, c, v)
        BY <3>3
      <3>5. PICK R \in Quorum :
               \A a \in R : VotedFor(a, c, w)
        BY <2>1 DEF ChosenIn
      <3>6. Q \cap R # {}
        BY <3>4, <3>5, QA
      <3>7. PICK a \in Q \cap R : TRUE
        BY <3>6
      <3>8. a \in Acceptor
        BY <3>4, <3>7, QA
      <3>9. /\ VotedFor(a, c, w)
             /\ (DidNotVoteIn(a, c) \/ VotedFor(a, c, v))
        BY <3>4, <3>5, <3>7
      <3>10. QED
        BY <1>1, <2>1, <3>8, <3>9, OneAcceptorValue
    <2>2. QED
      BY <2>1
  <1>2. QED
    BY <1>1

LEMMA ChosenSafe ==
  VInv2 =>
    \A b \in Ballot, v \in Value : ChosenIn(b, v) => SafeAt(b, v)
PROOF
  <1>1. ASSUME VInv2
        PROVE  \A b \in Ballot, v \in Value : ChosenIn(b, v) => SafeAt(b, v)
    <2>1. ASSUME NEW b \in Ballot, NEW v \in Value, ChosenIn(b, v)
          PROVE  SafeAt(b, v)
      <3>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
        BY <2>1 DEF ChosenIn
      <3>2. Q # {}
        BY <3>1, QuorumNonEmpty
      <3>3. PICK a \in Q : TRUE
        BY <3>2
      <3>4. a \in Acceptor
        BY <3>1, <3>3, QA
      <3>5. VotedFor(a, b, v)
        BY <3>1, <3>3
      <3>6. QED
        BY <1>1, <2>1, <3>4, <3>5 DEF VInv2
    <2>2. QED
      BY <2>1
  <1>2. QED
    BY <1>1

LEMMA SameBallotChosen ==
  VInv1 =>
    \A b \in Ballot, v, w \in Value :
      ChosenIn(b, v) /\ ChosenIn(b, w) => v = w
PROOF
  <1>1. ASSUME VInv1
        PROVE  \A b \in Ballot, v, w \in Value :
                 ChosenIn(b, v) /\ ChosenIn(b, w) => v = w
    <2>1. ASSUME NEW b \in Ballot, NEW v \in Value, NEW w \in Value,
                  ChosenIn(b, v), ChosenIn(b, w)
          PROVE  v = w
      <3>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
        BY <2>1 DEF ChosenIn
      <3>2. PICK R \in Quorum : \A a \in R : VotedFor(a, b, w)
        BY <2>1 DEF ChosenIn
      <3>3. Q \cap R # {}
        BY <3>1, <3>2, QA
      <3>4. PICK a \in Q \cap R : TRUE
        BY <3>3
      <3>5. a \in Acceptor
        BY <3>1, <3>4, QA
      <3>6. /\ VotedFor(a, b, v)
             /\ VotedFor(a, b, w)
        BY <3>1, <3>2, <3>4
      <3>7. QED
        BY <1>1, <2>1, <3>5, <3>6 DEF VInv1
    <2>2. QED
      BY <2>1
  <1>2. QED
    BY <1>1

-----------------------------------------------------------------------------

THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
PROOF
  <1>1. ASSUME TypeOK, VInv1, VInv2
        PROVE  \A v, w : (v \in chosen) /\ (w \in chosen) => (v = w)
    <2>1. ASSUME NEW v, NEW w,
                  v \in chosen,
                  w \in chosen
          PROVE  v = w
      <3>1. v \in Value
        BY <2>1 DEF chosen
      <3>2. w \in Value
        BY <2>1 DEF chosen
      <3>3. PICK b \in Ballot : ChosenIn(b, v)
        BY <2>1 DEF chosen
      <3>4. PICK c \in Ballot : ChosenIn(c, w)
        BY <2>1 DEF chosen
      <3>5. CASE b = c
        <4>1. ChosenIn(b, w)
          BY <3>4, <3>5
        <4>2. QED
          BY <1>1, <3>1, <3>2, <3>3, <4>1, SameBallotChosen
      <3>6. CASE b > c
        <4>1. SafeAt(b, v)
          BY <1>1, <3>1, <3>3, ChosenSafe
        <4>2. QED
          BY <1>1, <3>1, <3>2, <3>4, <3>6, <4>1, VT0
      <3>7. CASE c > b
        <4>1. SafeAt(c, w)
          BY <1>1, <3>2, <3>4, ChosenSafe
        <4>2. w = v
          BY <1>1, <3>1, <3>2, <3>3, <3>7, <4>1, VT0
        <4>3. QED
          BY <4>2
      <3>8. QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, SMT DEF Ballot
    <2>2. QED
      BY <2>1
  <1>2. QED
    BY <1>1

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}
-----------------------------------------------------------------------------

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

AXIOM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)
-----------------------------------------------------------------------------

-------------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

===============================================================================
