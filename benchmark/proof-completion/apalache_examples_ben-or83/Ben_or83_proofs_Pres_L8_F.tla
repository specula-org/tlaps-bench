---- MODULE Ben_or83_proofs_Pres_L8_F ----
EXTENDS Ben_or83_proofs_Pres_L8_FScaffold
THEOREM Pres_L8_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
