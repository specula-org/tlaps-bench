---- MODULE Paxos_Refinement ----
EXTENDS Paxos_RefinementDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Refinement == Spec => C!Spec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
