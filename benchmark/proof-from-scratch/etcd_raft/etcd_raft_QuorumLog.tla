---------------------------- MODULE etcd_raft_QuorumLog ----------------------------
EXTENDS EtcdRaft

THEOREM Spec => []QuorumLogInv
PROOF OBVIOUS

=============================================================================
