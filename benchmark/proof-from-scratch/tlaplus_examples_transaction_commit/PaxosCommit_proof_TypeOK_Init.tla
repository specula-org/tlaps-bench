---- MODULE PaxosCommit_proof_TypeOK_Init ----
EXTENDS PaxosCommit_proof_TypeOK_InitDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeOK_Init == PCSpec => PCTypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
