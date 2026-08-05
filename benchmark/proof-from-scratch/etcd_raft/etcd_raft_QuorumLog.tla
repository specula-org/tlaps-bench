---- MODULE etcd_raft_QuorumLog ----
EXTENDS etcd_raft_QuorumLogDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM QuorumLog == Spec => []QuorumLogInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
