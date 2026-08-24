---- MODULE ivy_examples_ticket_Safety ----
EXTENDS ivy_examples_ticket_SafetyDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == SafetySpec => []MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
