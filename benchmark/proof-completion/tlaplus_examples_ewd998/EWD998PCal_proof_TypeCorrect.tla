---- MODULE EWD998PCal_proof_TypeCorrect ----
EXTENDS EWD998PCal_proof_TypeCorrectScaffold
USE NAssumption
THEOREM TypeCorrect == Spec => []PCalTypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
