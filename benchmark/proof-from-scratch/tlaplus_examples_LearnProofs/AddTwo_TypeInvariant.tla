---- MODULE AddTwo_TypeInvariant ----
EXTENDS AddTwo_TypeInvariantDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeInvariant == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
