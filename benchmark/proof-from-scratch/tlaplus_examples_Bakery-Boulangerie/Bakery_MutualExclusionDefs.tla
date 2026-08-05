------------ MODULE Bakery_MutualExclusionDefs ----------------------------

EXTENDS BakeryModel

MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"

=============================================================================

Test 1:  5248 distinct initial states  151056 full initial states
IInit == TypeOK /\ IInv 
