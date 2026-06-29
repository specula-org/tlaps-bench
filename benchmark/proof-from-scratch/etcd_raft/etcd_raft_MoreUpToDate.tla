-------------------------- MODULE etcd_raft_MoreUpToDate --------------------------
EXTENDS EtcdRaft

THEOREM Spec => []MoreUpToDateCorrectInv
PROOF OBVIOUS

=============================================================================
