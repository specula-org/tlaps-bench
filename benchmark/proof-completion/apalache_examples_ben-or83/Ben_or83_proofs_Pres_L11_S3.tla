---- MODULE Ben_or83_proofs_Pres_L11_S3 ----
EXTENDS Ben_or83_proofs_Pres_L11_S3Scaffold
THEOREM Pres_L11_S3 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step3(id0)
  PROVE  Lemma11_ValueOnQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
