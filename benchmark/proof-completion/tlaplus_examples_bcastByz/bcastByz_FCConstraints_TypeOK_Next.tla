---- MODULE bcastByz_FCConstraints_TypeOK_Next ----
EXTENDS bcastByz_FCConstraints_TypeOK_NextScaffold
THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
