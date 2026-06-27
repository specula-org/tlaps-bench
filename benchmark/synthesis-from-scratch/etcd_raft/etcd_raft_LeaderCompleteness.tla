----------------------- MODULE etcd_raft_LeaderCompleteness -----------------------
EXTENDS EtcdRaft

THEOREM Spec => []LeaderCompletenessInv
PROOF OBVIOUS

=============================================================================
