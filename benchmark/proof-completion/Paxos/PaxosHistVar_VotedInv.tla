---- MODULE PaxosHistVar_VotedInv ----
EXTENDS PaxosHistVar_VotedInvScaffold
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
