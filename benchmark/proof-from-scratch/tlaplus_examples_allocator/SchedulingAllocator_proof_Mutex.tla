---- MODULE SchedulingAllocator_proof_Mutex ----
EXTENDS SchedulingAllocator_proof_MutexDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Mutex == Allocator => []ResourceMutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
