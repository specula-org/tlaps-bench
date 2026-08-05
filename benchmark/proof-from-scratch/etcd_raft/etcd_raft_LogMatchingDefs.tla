--------------------------------- MODULE etcd_raft_LogMatchingDefs ---------------------------------

EXTENDS etcd_raftModel

LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

===============================================================================

