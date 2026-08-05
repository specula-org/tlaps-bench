---- MODULE Ben_or83_proofs_Pres_L9_S3 ----
EXTENDS Ben_or83_proofs_Pres_L9_S3Scaffold
THEOREM Pres_L9_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma9_RoundsConnection'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
