---- MODULE SimpleAllocator_proof_TypeCorrect ----
EXTENDS SimpleAllocator_proof_TypeCorrectScaffold
THEOREM TypeCorrect == SimpleAllocator => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
