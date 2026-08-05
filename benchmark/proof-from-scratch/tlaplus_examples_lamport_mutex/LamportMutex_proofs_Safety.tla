---- MODULE LamportMutex_proofs_Safety ----
EXTENDS LamportMutex_proofs_SafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == Spec => []Mutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
