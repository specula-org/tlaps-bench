------------ MODULE AtomicBakeryWithoutSMT_Safety ----------------------------

EXTENDS AtomicBakeryWithoutSMT

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "p7"
                                               /\ pc[j] = "p7"

THEOREM Safety == Spec => [] MutualExclusion
PROOF OBVIOUS

=============================================================================
