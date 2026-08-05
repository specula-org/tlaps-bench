---- MODULE Ben_or83_proofs_Pres_L1_F ----
EXTENDS Ben_or83_proofs_Pres_L1_FScaffold
THEOREM Pres_L1_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
