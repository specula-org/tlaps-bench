---- MODULE etcd_raft_CommittedIsDurable ----
EXTENDS etcd_raft_CommittedIsDurableDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CommittedIsDurable == Spec => []CommittedIsDurableInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
