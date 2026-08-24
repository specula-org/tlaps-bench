---- MODULE InternalMemory_proof_TypeCorrect ----
EXTENDS InternalMemory_proof_TypeCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == ISpec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
