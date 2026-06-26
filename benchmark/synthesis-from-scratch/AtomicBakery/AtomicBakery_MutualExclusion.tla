------------ MODULE AtomicBakery_MutualExclusion ----------------------------

EXTENDS AtomicBakery

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"

THEOREM Spec => []MutualExclusion
PROOF OBVIOUS
=============================================================================

