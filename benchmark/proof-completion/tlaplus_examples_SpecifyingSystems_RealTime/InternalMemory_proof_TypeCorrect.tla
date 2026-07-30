---- MODULE InternalMemory_proof_TypeCorrect ----
EXTENDS InternalMemory_proof_TypeCorrectScaffold
THEOREM TypeCorrect == ISpec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
