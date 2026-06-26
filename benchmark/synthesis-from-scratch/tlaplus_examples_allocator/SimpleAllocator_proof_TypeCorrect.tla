----------------------- MODULE SimpleAllocator_proof_TypeCorrect -----------------------

EXTENDS SimpleAllocator, TLAPS

THEOREM TypeCorrect == SimpleAllocator => []TypeInvariant
PROOF OBVIOUS

============================================================================
