---- MODULE Ben_or83_proofs_Pres_L4_S3 ----
EXTENDS Ben_or83_proofs_Pres_L4_S3Scaffold
THEOREM Pres_L4_S3 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma4_MessagesNotFromFuture'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
