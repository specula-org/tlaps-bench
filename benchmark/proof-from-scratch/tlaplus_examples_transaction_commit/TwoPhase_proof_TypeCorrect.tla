--------------------------- MODULE TwoPhase_proof_TypeCorrect --------------------------

EXTENDS TwoPhase, TLAPS

THEOREM TypeCorrect == TPSpec => []TPTypeOK
PROOF OBVIOUS

============================================================================
