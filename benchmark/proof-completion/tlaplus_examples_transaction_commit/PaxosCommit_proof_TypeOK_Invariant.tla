---- MODULE PaxosCommit_proof_TypeOK_Invariant ----
EXTENDS PaxosCommit_proof_TypeOK_InvariantScaffold
THEOREM TypeOK_Invariant == PCSpec => []PCTypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
