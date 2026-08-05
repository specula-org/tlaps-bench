----------------------------- MODULE VoteProof_VT3Defs ------------------------------

EXTENDS VoteProofModel

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}

C == INSTANCE Consensus 

===============================================================================
