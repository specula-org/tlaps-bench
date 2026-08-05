---- MODULE Ben_or83_proofs_Pres_Lemma2 ----
EXTENDS Ben_or83_proofs_Pres_Lemma2Scaffold
THEOREM Pres_Lemma2 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
