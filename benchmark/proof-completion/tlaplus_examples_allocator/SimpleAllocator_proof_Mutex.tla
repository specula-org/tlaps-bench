---- MODULE SimpleAllocator_proof_Mutex ----
EXTENDS SimpleAllocator_proof_MutexScaffold
THEOREM Mutex == SimpleAllocator => []ResourceMutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
