---- MODULE Ben_or83_proofs_Pres_L7_S1 ----
EXTENDS Ben_or83_proofs_Pres_L7_S1Scaffold
THEOREM Pres_L7_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma7_D2RequiresQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
