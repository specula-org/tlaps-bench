---- MODULE Boulanger_TypeCorrect ----
EXTENDS Boulanger_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
