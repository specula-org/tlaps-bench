------------ MODULE Bakery_MutualExclusion ----------------------------

EXTENDS Bakery

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"

THEOREM Spec => []MutualExclusion
PROOF OBVIOUS

=============================================================================

Test 1:  5248 distinct initial states  151056 full initial states
IInit == TypeOK /\ IInv 
