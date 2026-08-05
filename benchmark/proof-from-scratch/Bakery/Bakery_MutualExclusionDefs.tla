----------------------------- MODULE Bakery_MutualExclusionDefs ---------------------------------

EXTENDS BakeryModel

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"

=============================================================================
