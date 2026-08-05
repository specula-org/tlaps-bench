---- MODULE Ben_or83_proofs_Pres_L9_F ----
EXTENDS Ben_or83_proofs_Pres_L9_FScaffold
THEOREM Pres_L9_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma9_RoundsConnection'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
