------------------------- MODULE InnerFIFO_proof_TypeCorrect ---------------------------

EXTENDS InnerFIFO, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
