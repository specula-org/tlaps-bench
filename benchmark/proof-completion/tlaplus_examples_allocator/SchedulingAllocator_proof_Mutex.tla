---- MODULE SchedulingAllocator_proof_Mutex ----
EXTENDS SchedulingAllocator_proof_MutexScaffold
THEOREM Mutex == Allocator => []ResourceMutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
