---- MODULE TPaxosWithProof_Invariant ----
EXTENDS TPaxosWithProof_InvariantDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Invariant == Spec => []Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
