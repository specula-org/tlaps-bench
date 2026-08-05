---- MODULE SimpleAllocator_proof_Mutex ----
EXTENDS SimpleAllocator_proof_MutexDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Mutex == SimpleAllocator => []ResourceMutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
