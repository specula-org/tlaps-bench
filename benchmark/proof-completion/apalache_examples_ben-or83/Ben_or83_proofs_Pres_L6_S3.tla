---- MODULE Ben_or83_proofs_Pres_L6_S3 ----
EXTENDS Ben_or83_proofs_Pres_L6_S3Scaffold
THEOREM Pres_L6_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma6_DecisionDefinesValue'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
