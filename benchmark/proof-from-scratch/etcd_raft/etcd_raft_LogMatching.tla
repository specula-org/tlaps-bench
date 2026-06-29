--------------------------- MODULE etcd_raft_LogMatching ---------------------------
EXTENDS EtcdRaft

THEOREM Spec => []LogMatchingInv
PROOF OBVIOUS

=============================================================================
