---- MODULE Ben_or83_proofs_Pres_L7_S3 ----
EXTENDS Ben_or83_proofs_Pres_L7_S3Scaffold
THEOREM Pres_L7_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma7_D2RequiresQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
