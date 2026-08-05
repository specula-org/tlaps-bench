---- MODULE Ben_or83_proofs_Pres_L10_F ----
EXTENDS Ben_or83_proofs_Pres_L10_FScaffold
THEOREM Pres_L10_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma10_M1RequiresQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
