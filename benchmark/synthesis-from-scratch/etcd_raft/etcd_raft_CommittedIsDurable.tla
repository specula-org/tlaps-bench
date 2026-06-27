----------------------- MODULE etcd_raft_CommittedIsDurable -----------------------
EXTENDS EtcdRaft

THEOREM Spec => []CommittedIsDurableInv
PROOF OBVIOUS

=============================================================================
