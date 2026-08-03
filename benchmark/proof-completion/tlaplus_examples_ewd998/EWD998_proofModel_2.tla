---------------------------- MODULE EWD998_proofModel_2 ----------------------------

EXTENDS EWD998, FiniteSetTheorems, TLAPS

BSpec ==
  /\ []TypeOK
  /\ []Inv
  /\ [][Next]_vars
  /\ []~terminationDetected
  /\ WF_vars(System)

=============================================================================
