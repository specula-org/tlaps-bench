------------------------------ MODULE GermanData_Refinement ------------------------------
EXTENDS GermanData

Abstract == INSTANCE GermanControl WITH
    cache <- [i \in NODE |-> cache[i].state],
    chan1 <- [i \in NODE |-> chan1[i].cmd],
    chan2 <- [i \in NODE |-> chan2[i].cmd],
    chan3 <- [i \in NODE |-> chan3[i].cmd]

Refinement == Abstract!Spec

THEOREM Spec => Refinement
PROOF OBVIOUS

=============================================================================
