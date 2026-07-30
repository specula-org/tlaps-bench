---- MODULE TPaxosWithProof_MsgNotLost ----
EXTENDS TPaxosWithProof_MsgNotLostScaffold
LEMMA MsgNotLost == Next /\ TypeOK =>
        \A m \in msgs, b1 \in Ballot, p1 \in Participant, v1 \in Value:
                       /\ m.from = p1
                       /\ m.state[p1].maxBal = b1
                       /\ m.state[p1].maxVBal = b1
                       /\ m.state[p1].maxVVal = v1
                       => m \in msgs'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
