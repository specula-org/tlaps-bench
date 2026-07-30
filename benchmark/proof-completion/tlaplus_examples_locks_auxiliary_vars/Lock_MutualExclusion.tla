---- MODULE Lock_MutualExclusion ----
EXTENDS Lock_MutualExclusionScaffold
THEOREM MutualExclusion == Spec => []LockInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
