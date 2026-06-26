------------------------------- MODULE Paxos_Refinement -------------------------------

EXTENDS Paxos

VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar

THEOREM Refinement == Spec => C!Spec
PROOF OBVIOUS
=============================================================================

