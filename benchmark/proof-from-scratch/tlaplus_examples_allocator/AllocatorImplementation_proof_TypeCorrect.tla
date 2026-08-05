---- MODULE AllocatorImplementation_proof_TypeCorrect ----
EXTENDS AllocatorImplementation_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Specification => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
