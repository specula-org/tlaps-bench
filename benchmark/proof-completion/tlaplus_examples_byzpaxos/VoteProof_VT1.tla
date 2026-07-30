---- MODULE VoteProof_VT1 ----
EXTENDS VoteProof_VT1Scaffold
THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
