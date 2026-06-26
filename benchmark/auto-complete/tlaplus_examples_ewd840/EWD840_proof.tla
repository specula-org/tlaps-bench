---------------------------- MODULE EWD840_proof ----------------------------

EXTENDS EWD840, NaturalsInduction, TLAPS
USE NAssumption

TSpec ==
    /\ []TypeOK
    /\ []Inv
    /\ []~terminationDetected
    /\ [][Next]_vars
    /\ WF_vars(System)

=============================================================================

