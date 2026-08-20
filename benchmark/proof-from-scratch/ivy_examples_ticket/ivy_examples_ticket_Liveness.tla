---- MODULE ivy_examples_ticket_Liveness ----
EXTENDS ivy_examples_ticket_LivenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == Spec => NonStarvation
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
