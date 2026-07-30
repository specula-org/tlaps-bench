---- MODULE EWD998_proof_TypeCorrect ----
EXTENDS EWD998_proof_TypeCorrectScaffold
USE NAssumption
THEOREM TypeCorrect == Init /\ [][Next]_vars => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
