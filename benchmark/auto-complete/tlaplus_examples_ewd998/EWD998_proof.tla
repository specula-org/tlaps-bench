---------------------------- MODULE EWD998_proof ----------------------------

EXTENDS EWD998, FiniteSetTheorems, TLAPS

USE NAssumption

BSpec ==
  /\ []TypeOK
  /\ []Inv
  /\ [][Next]_vars
  /\ []~terminationDetected
  /\ WF_vars(System)

=============================================================================

