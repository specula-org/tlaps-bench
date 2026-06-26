----------------------- MODULE SimpleAllocator_proof_Mutex -----------------------

EXTENDS SimpleAllocator, TLAPS

THEOREM Mutex == SimpleAllocator => []ResourceMutex
PROOF OBVIOUS

============================================================================
