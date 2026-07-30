---- MODULE TwoPhase_proof_TypeCorrect ----
EXTENDS TwoPhase_proof_TypeCorrectScaffold
THEOREM TypeCorrect == TPSpec => []TPTypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
