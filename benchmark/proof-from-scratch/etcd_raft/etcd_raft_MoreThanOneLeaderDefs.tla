--------------------------------- MODULE etcd_raft_MoreThanOneLeaderDefs ---------------------------------

EXTENDS etcd_raftModel

MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

===============================================================================

