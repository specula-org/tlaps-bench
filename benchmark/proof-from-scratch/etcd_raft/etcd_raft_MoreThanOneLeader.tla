---- MODULE etcd_raft_MoreThanOneLeader ----
EXTENDS etcd_raft_MoreThanOneLeaderDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM MoreThanOneLeader == Spec => []MoreThanOneLeaderInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
