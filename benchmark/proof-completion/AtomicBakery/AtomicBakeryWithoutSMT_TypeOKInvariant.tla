---- MODULE AtomicBakeryWithoutSMT_TypeOKInvariant ----
EXTENDS AtomicBakeryWithoutSMT_TypeOKInvariantScaffold
THEOREM TypeOKInvariant ==
        ASSUME TypeOK,
               Next
        PROVE  TypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
