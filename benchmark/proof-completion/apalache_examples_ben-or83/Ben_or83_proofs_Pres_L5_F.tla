---- MODULE Ben_or83_proofs_Pres_L5_F ----
EXTENDS Ben_or83_proofs_Pres_L5_FScaffold
THEOREM Pres_L5_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma5_RoundNeedsSentMessages'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
