--------------------------- MODULE SimpleRegular_proof_TypeCorrect ------------------------

EXTENDS SimpleRegular, TLAPS

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

============================================================================
