---- MODULE Ben_or83_proofs_Pres_L9_S1 ----
EXTENDS Ben_or83_proofs_Pres_L9_S1Scaffold
THEOREM Pres_L9_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma9_RoundsConnection'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
