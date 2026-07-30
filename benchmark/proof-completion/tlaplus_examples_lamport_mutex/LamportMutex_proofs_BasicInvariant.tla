---- MODULE LamportMutex_proofs_BasicInvariant ----
EXTENDS LamportMutex_proofs_BasicInvariantScaffold
USE DEF Clock
THEOREM BasicInvariant == Spec => []BasicInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
