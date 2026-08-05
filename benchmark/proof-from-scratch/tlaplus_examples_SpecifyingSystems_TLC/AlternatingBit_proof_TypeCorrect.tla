---- MODULE AlternatingBit_proof_TypeCorrect ----
EXTENDS AlternatingBit_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == ABSpec => []ABTypeInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
