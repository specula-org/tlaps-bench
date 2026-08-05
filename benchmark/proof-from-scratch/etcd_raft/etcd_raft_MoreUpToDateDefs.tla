--------------------------------- MODULE etcd_raft_MoreUpToDateDefs ---------------------------------

EXTENDS etcd_raftModel

Committed(i) == SubSeq(log[i],1,commitIndex[i])

MoreUpToDateCorrectInv ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

===============================================================================

