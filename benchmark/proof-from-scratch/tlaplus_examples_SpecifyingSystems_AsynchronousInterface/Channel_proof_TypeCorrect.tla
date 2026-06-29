--------------------------- MODULE Channel_proof_TypeCorrect ---------------------------

EXTENDS Channel, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
