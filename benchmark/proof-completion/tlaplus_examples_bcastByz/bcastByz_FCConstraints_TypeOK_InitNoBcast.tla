---- MODULE bcastByz_FCConstraints_TypeOK_InitNoBcast ----
EXTENDS bcastByz_FCConstraints_TypeOK_InitNoBcastScaffold
THEOREM FCConstraints_TypeOK_InitNoBcast == 
  InitNoBcast => FCConstraints /\ TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
