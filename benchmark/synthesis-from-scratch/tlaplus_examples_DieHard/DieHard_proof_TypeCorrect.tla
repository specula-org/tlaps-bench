--------------------------- MODULE DieHard_proof_TypeCorrect ------------------------------

EXTENDS DieHard, TLAPS

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
