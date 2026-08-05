---- MODULE Ben_or83_proofs_Pres_L5_S3 ----
EXTENDS Ben_or83_proofs_Pres_L5_S3Scaffold
THEOREM Pres_L5_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma5_RoundNeedsSentMessages'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
