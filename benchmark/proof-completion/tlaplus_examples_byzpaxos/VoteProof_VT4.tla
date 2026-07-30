---- MODULE VoteProof_VT4 ----
EXTENDS VoteProof_VT4Scaffold
THEOREM VT4 == TypeOK /\ VInv2 /\ VInv3  =>
                \A Q \in Quorum, b \in Ballot :
                   (\A a \in Q : (maxBal[a] >= b)) => \E v \in Value : SafeAt(b,v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
