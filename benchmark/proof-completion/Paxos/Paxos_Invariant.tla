---- MODULE Paxos_Invariant ----
EXTENDS Paxos_InvariantScaffold
THEOREM Invariant == Spec => []Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
