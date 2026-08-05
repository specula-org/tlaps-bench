--------------------------------- MODULE etcd_raft_CommittedIsDurableDefs ---------------------------------

EXTENDS etcd_raftModel

CommittedIsDurableInv ==
    \A i \in Server :
        state[i] = Leader => commitIndex[i] <= durableState[i].log

===============================================================================

