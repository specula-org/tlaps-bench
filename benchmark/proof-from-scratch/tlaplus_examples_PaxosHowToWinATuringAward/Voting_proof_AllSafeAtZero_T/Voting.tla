------------------------------ MODULE Voting ------------------------------- 

EXTENDS Integers, TLAPS

CONSTANTS Value, Acceptor, Quorum

ASSUME QuorumAssumption ==
       /\ \A Q \in Quorum : Q \subseteq Acceptor
       /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {} 

Ballot == Nat
-----------------------------------------------------------------------------

VARIABLES votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == 
   \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum : 
      \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

C == INSTANCE Consensus 
        WITH  Value <- Value,  chosen <- chosen 

=============================================================================
