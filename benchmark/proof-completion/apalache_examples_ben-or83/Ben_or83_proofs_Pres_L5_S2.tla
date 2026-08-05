---- MODULE Ben_or83_proofs_Pres_L5_S2 ----
EXTENDS Ben_or83_proofs_Pres_L5_S2Scaffold
THEOREM Pres_L5_S2 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step2(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
