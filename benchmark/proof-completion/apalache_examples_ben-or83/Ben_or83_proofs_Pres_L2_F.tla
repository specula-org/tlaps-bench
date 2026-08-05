---- MODULE Ben_or83_proofs_Pres_L2_F ----
EXTENDS Ben_or83_proofs_Pres_L2_FScaffold
THEOREM Pres_L2_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
