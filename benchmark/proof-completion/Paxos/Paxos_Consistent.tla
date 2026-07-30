---- MODULE Paxos_Consistent ----
EXTENDS Paxos_ConsistentScaffold
THEOREM Consistent == Spec => []Consistency
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
