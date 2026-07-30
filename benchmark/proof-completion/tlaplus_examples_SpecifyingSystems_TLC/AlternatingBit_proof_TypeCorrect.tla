---- MODULE AlternatingBit_proof_TypeCorrect ----
EXTENDS AlternatingBit_proof_TypeCorrectScaffold
THEOREM TypeCorrect == ABSpec => []ABTypeInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
