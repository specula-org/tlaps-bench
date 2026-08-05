---- MODULE Ben_or83_proofs_Pres_L3_F ----
EXTENDS Ben_or83_proofs_Pres_L3_FScaffold
THEOREM Pres_L3_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma3_NoEquivocation2ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
