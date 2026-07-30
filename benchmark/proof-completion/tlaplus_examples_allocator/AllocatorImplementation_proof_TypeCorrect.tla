---- MODULE AllocatorImplementation_proof_TypeCorrect ----
EXTENDS AllocatorImplementation_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Specification => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
