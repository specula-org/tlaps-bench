----------------------------- MODULE VoteProof_InitImpliesInv ------------------------------

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

Init == 
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)

VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4
-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

THEOREM InitImpliesInv == Init => VInv
<1> SUFFICES ASSUME Init
             PROVE  VInv
  OBVIOUS
<1>1. TypeOK
  BY DEF Init, TypeOK, Ballot
<1>2. VInv2
  <2> SUFFICES ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value,
                      VotedFor(a, b, v)
               PROVE  SafeAt(b, v)
    BY DEF VInv2
  <2>1. votes[a] = {}
    BY DEF Init
  <2> QED
    BY <2>1 DEF VotedFor
<1>3. VInv3
  <2> SUFFICES ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW b \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      VotedFor(a1, b, v1), VotedFor(a2, b, v2)
               PROVE  v1 = v2
    BY DEF VInv3
  <2>1. votes[a1] = {}
    BY DEF Init
  <2> QED
    BY <2>1 DEF VotedFor
<1>4. VInv4
  <2> SUFFICES ASSUME NEW a \in Acceptor, NEW b \in Ballot,
                      maxBal[a] < b
               PROVE  DidNotVoteIn(a, b)
    BY DEF VInv4
  <2> SUFFICES ASSUME NEW v \in Value
               PROVE  ~ VotedFor(a, b, v)
    BY DEF DidNotVoteIn
  <2>1. votes[a] = {}
    BY DEF Init
  <2> QED
    BY <2>1 DEF VotedFor
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF VInv

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

