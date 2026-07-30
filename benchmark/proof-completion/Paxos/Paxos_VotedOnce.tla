---- MODULE Paxos_VotedOnce ----
EXTENDS Paxos_VotedOnceScaffold
LEMMA VotedOnce == 
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
