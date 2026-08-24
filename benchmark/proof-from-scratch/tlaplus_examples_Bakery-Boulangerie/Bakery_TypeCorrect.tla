---- MODULE Bakery_TypeCorrect ----
EXTENDS Bakery_TypeCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
