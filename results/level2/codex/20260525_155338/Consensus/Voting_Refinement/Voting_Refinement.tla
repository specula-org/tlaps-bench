------------------------------- MODULE Voting_Refinement -------------------------------
EXTENDS FiniteSets, TLAPS, Integers
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
-----------------------------------------------------------------------------
VARIABLES votes, maxBal

-----------------------------------------------------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b 
  /\ \E c \in -1..(b-1) :
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
Init == 
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b] 
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
    /\ maxBal[a] <= b 
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v) 
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}] 
    /\ maxBal' = [maxBal EXCEPT ![a] = b] 
-----------------------------------------------------------------------------
Next == 
    \E a \in Acceptor, b \in Ballot : 
        \/ IncreaseMaxBal(a, b)
        \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>
-----------------------------------------------------------------------------
ChosenAt(b, v) == 
    \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

---------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
V == INSTANCE Voting

C == INSTANCE Consensus 

THEOREM Refinement == Spec => C!Spec
PROOF
<1>1. Spec => V!Spec
  BY DEF V!Spec, V!Init, V!Next, V!IncreaseMaxBal, V!VoteFor,
         V!ShowsSafeAt, V!DidNotVoteAt, V!VotedFor, V!Ballot,
         Spec, Init, Next, IncreaseMaxBal, VoteFor, ShowsSafeAt,
         DidNotVoteAt, VotedFor, Ballot
<1>2. V!C!Init => C!Init
  BY DEF V!C!Init, C!Init, V!chosen, chosen, V!ChosenAt, ChosenAt,
         V!VotedFor, VotedFor, V!Ballot, Ballot
<1>3. [][V!C!Next]_V!chosen => [][C!Next]_chosen
  BY PTL DEF V!C!Next, C!Next, V!chosen, chosen, V!ChosenAt, ChosenAt,
             V!VotedFor, VotedFor, V!Ballot, Ballot
<1>4. V!C!Spec => C!Spec
  BY <1>2, <1>3 DEF V!C!Spec, C!Spec
<1>5. Spec => V!C!Spec
  BY <1>1, V!Refinement, QuorumAssumption, PTL
<1>6. QED
  BY <1>4, <1>5, PTL
=============================================================================
