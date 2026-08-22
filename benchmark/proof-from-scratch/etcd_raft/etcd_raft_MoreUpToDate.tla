---- MODULE etcd_raft_MoreUpToDate ----
EXTENDS etcd_raft_MoreUpToDateDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM MoreUpToDate == Spec => []MoreUpToDateCorrectInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
