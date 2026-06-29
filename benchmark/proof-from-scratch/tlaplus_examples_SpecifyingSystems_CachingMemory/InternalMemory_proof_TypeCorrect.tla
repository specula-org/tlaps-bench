------------------------- MODULE InternalMemory_proof_TypeCorrect ----------------------

EXTENDS InternalMemory, TLAPS

THEOREM TypeCorrect == ISpec => []TypeInvariant
PROOF OBVIOUS

============================================================================
