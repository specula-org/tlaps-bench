------------------------ MODULE AlternatingBit_proof_TypeCorrect -----------------------

EXTENDS AlternatingBit, TLAPS

THEOREM TypeCorrect == ABSpec => []ABTypeInv
PROOF OBVIOUS

============================================================================
