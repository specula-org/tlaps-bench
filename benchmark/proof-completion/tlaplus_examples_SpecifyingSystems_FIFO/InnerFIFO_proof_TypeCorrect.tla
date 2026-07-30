---- MODULE InnerFIFO_proof_TypeCorrect ----
EXTENDS InnerFIFO_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Spec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
