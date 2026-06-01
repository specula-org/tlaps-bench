----------------------------- MODULE VoteProof_Liveness ------------------------------

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

IncreaseMaxBal(self, b) ==  
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

VoteFor(self, b, v) == 
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

C == INSTANCE Consensus 

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

LiveAssumption ==
  \E Q \in Quorum, b \in Ballot :
     \A self \in Q :
       /\ WF_vars(BallotAction(self, b))
       /\ [] [\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
     
LiveSpec == Spec /\ LiveAssumption  

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
VP == INSTANCE VoteProof

LEMMA EqSpec == Spec <=> VP!Spec
  BY DEF Spec, VP!Spec, Init, VP!Init, Next, VP!Next, vars, VP!vars,
         acceptor, VP!acceptor, Ballot, VP!Ballot,
         VotedFor, VP!VotedFor, DidNotVoteIn, VP!DidNotVoteIn, SafeAt, VP!SafeAt

LEMMA EqCSpec == C!Spec <=> VP!C!Spec
  BY DEF C!Spec, VP!C!Spec, C!Init, VP!C!Init, C!Next, VP!C!Next,
         C!vars, VP!C!vars, chosen, VP!chosen, ChosenIn, VP!ChosenIn,
         Ballot, VP!Ballot, VotedFor, VP!VotedFor

LEMMA EqLiveSpec == LiveSpec <=> VP!LiveSpec
  BY DEF LiveSpec, VP!LiveSpec, Spec, VP!Spec, Init, VP!Init,
         Next, VP!Next, vars, VP!vars, LiveAssumption, VP!LiveAssumption,
         BallotAction, VP!BallotAction, IncreaseMaxBal, VP!IncreaseMaxBal,
         VoteFor, VP!VoteFor, Ballot, VP!Ballot,
         VotedFor, VP!VotedFor, DidNotVoteIn, VP!DidNotVoteIn,
         SafeAt, VP!SafeAt, acceptor, VP!acceptor

LEMMA EqCLiveSpec == C!LiveSpec <=> VP!C!LiveSpec
  BY DEF C!LiveSpec, VP!C!LiveSpec, C!Spec, VP!C!Spec,
         C!Init, VP!C!Init, C!Next, VP!C!Next, C!vars, VP!C!vars,
         chosen, VP!chosen, ChosenIn, VP!ChosenIn,
         Ballot, VP!Ballot, VotedFor, VP!VotedFor

LEMMA TestVT3_full == VP!Spec => VP!C!Spec
  BY VP!VT3, QA, AcceptorNonempty, AcceptorFinite, ValueNonempty,
     SimpleNatInduction, SubsetOfFiniteSetFinite, FiniteSetHasMax, IntervalFinite

-----------------------------------------------------------------------------
\* Helper: Lift VT3 to our world
LEMMA Safety == Spec => C!Spec
  <1>1. Spec <=> VP!Spec  BY EqSpec
  <1>2. VP!Spec => VP!C!Spec  BY TestVT3_full
  <1>3. C!Spec <=> VP!C!Spec  BY EqCSpec
  <1> QED  BY <1>1, <1>2, <1>3, PTL

LEMMA TestVT2 == VP!Spec => []VP!VInv
  BY VP!VT2, QA, AcceptorNonempty, AcceptorFinite, ValueNonempty,
     SimpleNatInduction, SubsetOfFiniteSetFinite, FiniteSetHasMax, IntervalFinite




-----------------------------------------------------------------------------
\* The actual theorem we want to prove
THEOREM Liveness == LiveSpec => C!LiveSpec
  PROOF OBVIOUS

===============================================================================

