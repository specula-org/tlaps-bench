---- MODULE LamportMutex_proofs_ClockInvariant ----
EXTENDS LamportMutex_proofs_ClockInvariantScaffold
USE DEF Clock
THEOREM ClockInvariant == Spec => []ClockInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
