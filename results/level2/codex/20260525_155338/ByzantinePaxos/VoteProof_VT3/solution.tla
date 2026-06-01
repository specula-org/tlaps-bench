----------------------------- MODULE VoteProof_VT3 ------------------------------

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

vars == << votes, maxBal >>

Init == 
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
                    \/ /\ b > maxBal[self]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED votes
                    \/ /\ \E v \in Value:
                            /\ /\ maxBal[self] \leq b
                               /\ DidNotVoteIn(self, b)
                               /\ \A p \in Acceptor \ {self} :
                                     \A w \in Value : VotedFor(p, b, w) => (w = v)
                               /\ SafeAt(b, v)
                            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

V == INSTANCE VoteProof

C == INSTANCE Consensus 

LEMMA SafeAtVEq ==
  \A b \in Ballot, v \in Value : SafeAt(b, v) = V!SafeAt(b, v)
PROOF
  BY DEF SafeAt, V!SafeAt, Ballot, V!Ballot, VotedFor, V!VotedFor,
         DidNotVoteIn, V!DidNotVoteIn

LEMMA SpecVEq == Spec = V!Spec
PROOF
  BY SafeAtVEq
     DEF Spec, Init, Next, acceptor, vars, Ballot, VotedFor, DidNotVoteIn,
         SafeAt, V!Spec, V!Init, V!Next, V!acceptor, V!vars, V!Ballot,
         V!VotedFor, V!DidNotVoteIn, V!SafeAt

LEMMA ChosenVEq == chosen = V!chosen
PROOF
  BY DEF chosen, ChosenIn, VotedFor, Ballot, V!chosen, V!ChosenIn,
         V!VotedFor, V!Ballot

LEMMA ChosenVEqPrime == chosen' = V!chosen'
PROOF
  BY DEF chosen, ChosenIn, VotedFor, Ballot, V!chosen, V!ChosenIn,
         V!VotedFor, V!Ballot

LEMMA SpecImpliesVSpec == Spec => V!Spec
PROOF
  BY SpecVEq

LEMMA VVT3Usable == V!Spec => V!C!Spec
PROOF
  BY V!VT3, QA, AcceptorNonempty, SimpleNatInduction
     DEF V!VT3, QA, AcceptorNonempty, SimpleNatInduction

LEMMA VCInitImpliesCInit == V!C!Init => C!Init
PROOF
  BY ChosenVEq DEF C!Init, V!C!Init

LEMMA VCStepImpliesCStep ==
  TRUE /\ TRUE' /\ [V!C!Next]_V!C!vars => [C!Next]_C!vars
PROOF
  BY ChosenVEq, ChosenVEqPrime
     DEF C!Next, C!vars, V!C!Next, V!C!vars

LEMMA VCAlwaysStepImpliesCAlwaysStep ==
  [][V!C!Next]_V!C!vars => [][C!Next]_C!vars
PROOF
  BY VCStepImpliesCStep, PTL DEF VCStepImpliesCStep

LEMMA VCSpecImpliesCSpec == V!C!Spec => C!Spec
PROOF
  BY VCInitImpliesCInit, VCAlwaysStepImpliesCAlwaysStep
     DEF C!Spec, V!C!Spec

THEOREM VT3 == Spec => C!Spec 
PROOF
  <1>1. ASSUME Spec
        PROVE  C!Spec
    <2>1. V!Spec
      BY <1>1, SpecImpliesVSpec
    <2>2. V!C!Spec
      BY <2>1, VVT3Usable DEF VVT3Usable
    <2>3. QED
      BY <2>2, VCSpecImpliesCSpec DEF VCSpecImpliesCSpec
  <1>2. QED
    BY <1>1
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
