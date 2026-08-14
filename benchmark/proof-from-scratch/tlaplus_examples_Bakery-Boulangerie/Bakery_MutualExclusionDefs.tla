------------ MODULE Bakery_MutualExclusionDefs ----------------------------

EXTENDS BakeryModel

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"

=============================================================================
