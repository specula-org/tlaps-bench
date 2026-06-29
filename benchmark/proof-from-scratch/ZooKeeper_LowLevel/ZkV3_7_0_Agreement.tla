------------------------ MODULE ZkV3_7_0_Agreement ------------------------

EXTENDS ZkV3_7_0

TxnEqual(txn1, txn2) == /\ ZxidEqual(txn1.zxid, txn2.zxid)
                        /\ txn1.value = txn2.value

Agreement == \A i, j \in Server:
                /\ IsFollower(i) /\ lastCommitted[i].index > 0
                /\ IsFollower(j) /\ lastCommitted[j].index > 0
                =>
                \A idx1 \in 1..lastCommitted[i].index, idx2 \in 1..lastCommitted[j].index :
                    \/ \E idx_j \in 1..lastCommitted[j].index:
                        TxnEqual(history[j][idx_j], history[i][idx1])
                    \/ \E idx_i \in 1..lastCommitted[i].index:
                        TxnEqual(history[i][idx_i], history[j][idx2])

THEOREM Spec => []Agreement
PROOF OBVIOUS

=============================================================================
