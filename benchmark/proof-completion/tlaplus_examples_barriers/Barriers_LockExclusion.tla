---- MODULE Barriers_LockExclusion ----
EXTENDS Barriers_LockExclusionScaffold
LEMMA LockExclusion == Spec => []LockInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
