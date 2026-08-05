---- MODULE Ben_or83_proofs_Pres_L3_S3 ----
EXTENDS Ben_or83_proofs_Pres_L3_S3Scaffold
THEOREM Pres_L3_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
