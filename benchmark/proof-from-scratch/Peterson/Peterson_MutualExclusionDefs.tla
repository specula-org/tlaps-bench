--------------------------- MODULE Peterson_MutualExclusionDefs  ----------------------------

EXTENDS PetersonModel

MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

=============================================================================
