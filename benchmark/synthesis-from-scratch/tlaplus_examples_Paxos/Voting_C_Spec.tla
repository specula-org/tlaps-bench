------------------------------- MODULE Voting_C_Spec -------------------------------

EXTENDS Voting

ChosenAt(b, v) == \E Q \in Quorum : 
                     \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

C == INSTANCE Consensus

THEOREM Spec => C!Spec 
PROOF OBVIOUS

=============================================================================

