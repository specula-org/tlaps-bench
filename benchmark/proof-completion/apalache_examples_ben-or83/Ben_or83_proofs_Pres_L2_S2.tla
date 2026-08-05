---- MODULE Ben_or83_proofs_Pres_L2_S2 ----
EXTENDS Ben_or83_proofs_Pres_L2_S2Scaffold
THEOREM Pres_L2_S2 ==
  ASSUME IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
