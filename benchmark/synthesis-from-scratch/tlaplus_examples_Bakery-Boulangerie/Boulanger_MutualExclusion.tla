------------------------------ MODULE Boulanger_MutualExclusion ----------------------------

EXTENDS Boulanger

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"

THEOREM Spec => []MutualExclusion
PROOF OBVIOUS
=============================================================================

