---- MODULE SimpleMutex_Safety ----
EXTENDS SimpleMutex_SafetyScaffold
THEOREM Safety == Spec => []MutualExclusion
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
