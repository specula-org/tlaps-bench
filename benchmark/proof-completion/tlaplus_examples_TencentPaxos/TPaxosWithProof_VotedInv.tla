---- MODULE TPaxosWithProof_VotedInv ----
EXTENDS TPaxosWithProof_VotedInvScaffold
LEMMA VotedInv ==
        MsgInv /\ TypeOK =>
            \A a \in Participant, b \in Ballot, v \in Value:
                VotedForIn(a, b, v) => SafeAt(b, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
