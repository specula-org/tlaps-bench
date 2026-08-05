---- MODULE Ben_or83_proofs_Pres_L13_S1 ----
EXTENDS Ben_or83_proofs_Pres_L13_S1Scaffold
THEOREM Pres_L13_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma13_ValueLock'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
