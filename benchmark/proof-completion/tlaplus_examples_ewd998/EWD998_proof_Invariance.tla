---- MODULE EWD998_proof_Invariance ----
EXTENDS EWD998_proof_InvarianceScaffold
USE NAssumption
THEOREM Invariance == Init /\ [][Next]_vars => []Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
