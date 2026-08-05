---- MODULE etcd_raft_ElectionSafety ----
EXTENDS etcd_raft_ElectionSafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM ElectionSafety == Spec => []ElectionSafetyInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
