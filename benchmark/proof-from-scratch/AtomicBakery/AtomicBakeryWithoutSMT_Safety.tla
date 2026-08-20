---- MODULE AtomicBakeryWithoutSMT_Safety ----
EXTENDS AtomicBakeryWithoutSMT_SafetyDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == Spec => [] MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
