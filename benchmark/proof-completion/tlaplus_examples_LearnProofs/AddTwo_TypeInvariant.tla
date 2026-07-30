---- MODULE AddTwo_TypeInvariant ----
EXTENDS AddTwo_TypeInvariantScaffold
THEOREM TypeInvariant == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
