---- MODULE VoteProof_VT1Prime ----
EXTENDS VoteProof_VT1PrimeScaffold
THEOREM VT1Prime == 
               /\ TypeOK' 
               /\ VInv1'
               /\ VInv2'
               => \A v, w : 
                    (v \in chosen') /\ (w \in chosen') => (v = w)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
