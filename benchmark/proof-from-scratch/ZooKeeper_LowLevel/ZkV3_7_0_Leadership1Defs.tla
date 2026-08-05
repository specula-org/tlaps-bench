------------------------ MODULE ZkV3_7_0_Leadership1Defs ------------------------

EXTENDS ZkV3_7_0Model

Leadership1 == \A i, j \in Server:
                   /\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                   /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                   /\ acceptedEpoch[i] = acceptedEpoch[j]
                  => i = j

=============================================================================
