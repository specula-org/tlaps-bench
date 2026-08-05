---- MODULE TwoPhase_proof_TypeCorrect ----
EXTENDS TwoPhase_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == TPSpec => []TPTypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
