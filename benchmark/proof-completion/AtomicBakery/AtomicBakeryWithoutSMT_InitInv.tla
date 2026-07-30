---- MODULE AtomicBakeryWithoutSMT_InitInv ----
EXTENDS AtomicBakeryWithoutSMT_InitInvScaffold
THEOREM InitInv == Init => Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
