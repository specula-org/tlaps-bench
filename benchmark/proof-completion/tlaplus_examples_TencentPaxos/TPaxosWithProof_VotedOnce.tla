---- MODULE TPaxosWithProof_VotedOnce ----
EXTENDS TPaxosWithProof_VotedOnceScaffold
LEMMA VotedOnce ==
        MsgInv => \A a1, a2 \in Participant, b \in Ballot, v1, v2 \in Value:
                VotedForIn(a1, b, v1) /\ VotedForIn(a2, b, v2) => (v1 = v2)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
