---- MODULE PaxosCommit_proof_InitInv ----
EXTENDS PaxosCommit_proof_InitInvScaffold
LEMMA InitInv == PCInit => Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
