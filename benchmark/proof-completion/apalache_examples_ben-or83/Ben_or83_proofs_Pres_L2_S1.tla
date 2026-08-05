---- MODULE Ben_or83_proofs_Pres_L2_S1 ----
EXTENDS Ben_or83_proofs_Pres_L2_S1Scaffold
THEOREM Pres_L2_S1 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
