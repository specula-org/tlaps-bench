---- MODULE Ben_or83_proofs_Pres_L13_F ----
EXTENDS Ben_or83_proofs_Pres_L13_FScaffold
THEOREM Pres_L13_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma13_ValueLock'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
