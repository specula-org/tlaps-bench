---- MODULE ivy_examples_tlb_Safety ----
EXTENDS ivy_examples_tlb_SafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == SafetySpec => []NoError
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
