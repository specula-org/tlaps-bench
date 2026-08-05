--------------------------------- MODULE etcd_raft_ElectionSafetyDefs ---------------------------------

EXTENDS etcd_raftModel

MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})

===============================================================================

