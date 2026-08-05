---- MODULE Ben_or83_proofs_Pres_L7_F ----
EXTENDS Ben_or83_proofs_Pres_L7_FScaffold
THEOREM Pres_L7_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma7_D2RequiresQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
