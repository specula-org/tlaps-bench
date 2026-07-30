---- MODULE AtomicBakeryWithoutSMT_InductiveInvariant ----
EXTENDS AtomicBakeryWithoutSMT_InductiveInvariantScaffold
THEOREM InductiveInvariant == Inv /\ Next => Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
