---- MODULE AsynchInterface_proof_TypeCorrect ----
EXTENDS AsynchInterface_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Spec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
