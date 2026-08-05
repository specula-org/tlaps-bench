---- MODULE Ben_or83_proofs_Pres_L11_F ----
EXTENDS Ben_or83_proofs_Pres_L11_FScaffold
THEOREM Pres_L11_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma11_ValueOnQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
