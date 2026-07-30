---- MODULE PaxosCommit_proof_NextInv ----
EXTENDS PaxosCommit_proof_NextInvScaffold
LEMMA NextInv == Inv /\ [PCNext]_vars => Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
