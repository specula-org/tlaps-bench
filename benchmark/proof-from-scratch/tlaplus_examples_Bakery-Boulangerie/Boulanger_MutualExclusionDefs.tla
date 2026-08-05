------------------------------ MODULE Boulanger_MutualExclusionDefs ----------------------------

EXTENDS BoulangerModel

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"

=============================================================================

