---- MODULE Paxos_Refinement ----
EXTENDS Paxos_RefinementScaffold
THEOREM Refinement == Spec => C!Spec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
