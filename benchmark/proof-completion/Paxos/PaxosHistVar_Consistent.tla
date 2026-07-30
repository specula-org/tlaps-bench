---- MODULE PaxosHistVar_Consistent ----
EXTENDS PaxosHistVar_ConsistentScaffold
THEOREM Consistent == Spec => []Consistency
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
