---- MODULE TPaxosWithProof_Consistent ----
EXTENDS TPaxosWithProof_ConsistentScaffold
THEOREM Consistent == Spec => []Consistency
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
