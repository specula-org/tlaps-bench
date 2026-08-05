--------------------------- MODULE Zab_Leadership1Defs ---------------------------

EXTENDS ZabModel

Leadership1 == \A i, j \in Server:
                   /\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                   /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                   /\ currentEpoch[i] = currentEpoch[j]
                  => i = j

=============================================================================
