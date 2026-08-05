---- MODULE Lock_MutualExclusion ----
EXTENDS Lock_MutualExclusionDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM MutualExclusion == Spec => []LockInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
