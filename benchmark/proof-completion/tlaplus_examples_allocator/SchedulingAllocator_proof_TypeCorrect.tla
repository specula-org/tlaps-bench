---- MODULE SchedulingAllocator_proof_TypeCorrect ----
EXTENDS SchedulingAllocator_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Allocator => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
