------------ MODULE AtomicBakery_MutualExclusionDefs ----------------------------

EXTENDS AtomicBakeryModel

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"

=============================================================================

