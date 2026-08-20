---- MODULE SimpleAllocator_proof_TypeCorrect ----
EXTENDS SimpleAllocator_proof_TypeCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == SimpleAllocator => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
