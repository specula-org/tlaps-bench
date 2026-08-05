---- MODULE Ben_or83_proofs_Pres_L8_S3 ----
EXTENDS Ben_or83_proofs_Pres_L8_S3Scaffold
THEOREM Pres_L8_S3 ==
  ASSUME IndInv, NEW id \in CORRECT, Step3(id)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
