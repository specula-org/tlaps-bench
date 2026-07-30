---------------------------- MODULE EWD998_proofModel ----------------------------

EXTENDS EWD998, FiniteSetTheorems, TLAPS


BSpec ==
  /\ []TypeOK
  /\ []Inv
  /\ [][Next]_vars
  /\ []~terminationDetected
  /\ WF_vars(System)

=============================================================================

