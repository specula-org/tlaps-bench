---- MODULE Ben_or83_proofs_Pres_L2_S3 ----
EXTENDS Ben_or83_proofs_Pres_L2_S3Scaffold
THEOREM Pres_L2_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
