----------------------------- MODULE etcd_raft_LogInv -----------------------------
EXTENDS EtcdRaft

THEOREM Spec => []LogInv
PROOF OBVIOUS

=============================================================================
