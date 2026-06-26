--------------------------- MODULE ParReachProofs_line18 ---------------------------

EXTENDS ParReach, Integers, TLAPS

THEOREM Spec => R!Init /\ [][R!Next]_R!vars
PROOF OBVIOUS

=============================================================================

