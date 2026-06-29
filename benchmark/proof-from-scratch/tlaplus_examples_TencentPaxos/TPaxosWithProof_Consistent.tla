------------------------------ MODULE TPaxosWithProof_Consistent --------------------------------

EXTENDS TPaxosWithProof

VotedForIn(a, b, v) == \E m \in msgs:
                            /\ m.from = a
                            /\ m.state[a].maxBal = b
                            /\ m.state[a].maxVBal = b
                            /\ m.state[a].maxVVal = v

ChosenIn(b, v) == \E Q \in Quorum:
                    \A a \in Q: VotedForIn(a, b, v)

Chosen(v) == \E b \in Ballot: ChosenIn(b, v)

Consistency == 
   \A v1, v2 \in Value: Chosen(v1) /\ Chosen(v2) => (v1 = v2)

THEOREM Consistent == Spec => []Consistency
PROOF OBVIOUS

=============================================================================

