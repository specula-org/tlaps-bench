---- MODULE AtomicBakeryWithoutSMT_Safety ----
EXTENDS AtomicBakeryWithoutSMT_SafetyScaffold
THEOREM Safety == Spec => [] MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
