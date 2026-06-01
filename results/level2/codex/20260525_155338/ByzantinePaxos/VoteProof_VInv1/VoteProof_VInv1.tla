----------------------------- MODULE VoteProof_VInv1 ------------------------------

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

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

THEOREM VInv3 => VInv1
PROOF
<1>1. ASSUME VInv3
      PROVE  VInv1
  <2>1. SUFFICES ASSUME NEW a \in Acceptor,
                          NEW b \in Ballot,
                          NEW v \in Value,
                          NEW w \in Value
                   PROVE  VotedFor(a, b, v) /\ VotedFor(a, b, w) => v = w
    BY DEF VInv1
  <2>2. ASSUME VotedFor(a, b, v) /\ VotedFor(a, b, w)
        PROVE  v = w
    <3>1. VotedFor(a, b, v) /\ VotedFor(a, b, w) => v = w
      BY <1>1, <2>1 DEF VInv3
    <3>2. QED BY <2>2, <3>1
  <2>3. QED BY <2>1, <2>2 DEF VInv1
<1>2. QED BY <1>1
-----------------------------------------------------------------------------

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
