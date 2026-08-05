---- MODULE Ben_or83_proofs_Pres_L10_S3 ----
EXTENDS Ben_or83_proofs_Pres_L10_S3Scaffold
THEOREM Pres_L10_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma10_M1RequiresQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
