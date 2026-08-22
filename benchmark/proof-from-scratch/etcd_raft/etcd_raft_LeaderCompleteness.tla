---- MODULE etcd_raft_LeaderCompleteness ----
EXTENDS etcd_raft_LeaderCompletenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LeaderCompleteness == Spec => []LeaderCompletenessInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
