----------------------------- MODULE Bakery_MutualExclusion ---------------------------------

EXTENDS Bakery

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"

THEOREM Spec => []MutualExclusion
PROOF OBVIOUS
=============================================================================
