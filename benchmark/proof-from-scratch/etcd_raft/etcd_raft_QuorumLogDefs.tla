--------------------------------- MODULE etcd_raft_QuorumLogDefs ---------------------------------

EXTENDS etcd_raftModel

Committed(i) == SubSeq(log[i],1,commitIndex[i])

QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

===============================================================================

