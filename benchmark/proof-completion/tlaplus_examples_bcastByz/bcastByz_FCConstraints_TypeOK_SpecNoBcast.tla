---- MODULE bcastByz_FCConstraints_TypeOK_SpecNoBcast ----
EXTENDS bcastByz_FCConstraints_TypeOK_SpecNoBcastScaffold
THEOREM FCConstraints_TypeOK_SpecNoBcast == SpecNoBcast => [](FCConstraints /\ TypeOK)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
