---- MODULE Paxos_Consistent ----
EXTENDS Paxos_ConsistentDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Consistent == Spec => []Consistency
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
