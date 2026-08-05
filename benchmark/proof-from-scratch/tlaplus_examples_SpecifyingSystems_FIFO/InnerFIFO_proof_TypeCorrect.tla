---- MODULE InnerFIFO_proof_TypeCorrect ----
EXTENDS InnerFIFO_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Spec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
