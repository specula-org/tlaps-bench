---- MODULE Paxos_VotedInv ----
EXTENDS Paxos_VotedInvScaffold
LEMMA VotedInv ==
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b) /\ b =< maxVBal[a]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
