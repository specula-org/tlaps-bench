---- MODULE bcastByz_FCConstraints_TypeOK_Init ----
EXTENDS bcastByz_FCConstraints_TypeOK_InitDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM FCConstraints_TypeOK_Init == 
  Init => FCConstraints /\ TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
