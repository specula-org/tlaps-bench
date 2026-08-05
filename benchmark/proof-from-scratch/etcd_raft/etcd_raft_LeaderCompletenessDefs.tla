--------------------------------- MODULE etcd_raft_LeaderCompletenessDefs ---------------------------------

EXTENDS etcd_raftModel

CurrentLeaders == {i \in Server : state[i] = Leader}

Committed(i) == SubSeq(log[i],1,commitIndex[i])

LeaderCompletenessInv == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            
            \A l \in CurrentLeaders :
                
                currentTerm[l] > entry.term =>
                
                log[l][idx] = entry

===============================================================================

