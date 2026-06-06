--------------------------- MODULE Peterson_MutualExclusion  ----------------------------

EXTENDS Peterson

MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

USE DEF ProcSet

THEOREM Spec => []MutualExclusion
PROOF OBVIOUS

=============================================================================
