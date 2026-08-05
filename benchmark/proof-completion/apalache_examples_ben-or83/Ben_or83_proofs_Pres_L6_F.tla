---- MODULE Ben_or83_proofs_Pres_L6_F ----
EXTENDS Ben_or83_proofs_Pres_L6_FScaffold
THEOREM Pres_L6_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma6_DecisionDefinesValue'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
