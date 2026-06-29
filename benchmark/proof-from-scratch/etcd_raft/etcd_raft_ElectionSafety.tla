------------------------- MODULE etcd_raft_ElectionSafety -------------------------
EXTENDS EtcdRaft

THEOREM Spec => []ElectionSafetyInv
PROOF OBVIOUS

=============================================================================
