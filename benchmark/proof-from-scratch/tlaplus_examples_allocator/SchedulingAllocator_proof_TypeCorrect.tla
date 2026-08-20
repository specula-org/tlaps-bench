---- MODULE SchedulingAllocator_proof_TypeCorrect ----
EXTENDS SchedulingAllocator_proof_TypeCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Allocator => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
