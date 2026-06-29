------------------------ MODULE etcd_raft_MoreThanOneLeader ------------------------
EXTENDS EtcdRaft

THEOREM Spec => []MoreThanOneLeaderInv
PROOF OBVIOUS

=============================================================================
