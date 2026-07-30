---------------------------- MODULE EWD840_proofModel ----------------------------

EXTENDS EWD840, NaturalsInduction, TLAPS

TSpec ==
    /\ []TypeOK
    /\ []Inv
    /\ []~terminationDetected
    /\ [][Next]_vars
    /\ WF_vars(System)

=============================================================================

