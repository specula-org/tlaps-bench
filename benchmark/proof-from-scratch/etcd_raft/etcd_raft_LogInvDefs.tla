--------------------------------- MODULE etcd_raft_LogInvDefs ---------------------------------

EXTENDS etcd_raftModel

Committed(i) == SubSeq(log[i],1,commitIndex[i])

LogInv ==
    \A i, j \in Server :
        \/ IsPrefix(Committed(i),Committed(j)) 
        \/ IsPrefix(Committed(j),Committed(i))

===============================================================================

