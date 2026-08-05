---- MODULE ivy_examples_hybrid_reliable_broadcast_cisa_Safety ----
EXTENDS ivy_examples_hybrid_reliable_broadcast_cisa_SafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == SafetySpec => []Unforgeability
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
