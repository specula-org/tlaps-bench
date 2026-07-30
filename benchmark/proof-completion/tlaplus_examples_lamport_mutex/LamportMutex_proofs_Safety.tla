---- MODULE LamportMutex_proofs_Safety ----
EXTENDS LamportMutex_proofs_SafetyScaffold
USE DEF Clock
THEOREM Safety == Spec => []Mutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
