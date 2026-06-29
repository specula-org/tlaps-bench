------------------------ MODULE ZkV3_7_0_Leadership1 ------------------------

EXTENDS ZkV3_7_0

Leadership1 == \A i, j \in Server:
                   /\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                   /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                   /\ acceptedEpoch[i] = acceptedEpoch[j]
                  => i = j

THEOREM Spec => []Leadership1
PROOF OBVIOUS

=============================================================================
