---- MODULE etcd_raft_LogMatching ----
EXTENDS etcd_raft_LogMatchingDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LogMatching == Spec => []LogMatchingInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
