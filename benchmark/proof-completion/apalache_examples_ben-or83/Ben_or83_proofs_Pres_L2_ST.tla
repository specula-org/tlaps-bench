---- MODULE Ben_or83_proofs_Pres_L2_ST ----
EXTENDS Ben_or83_proofs_Pres_L2_STScaffold
THEOREM Pres_L2_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma2_NoEquivocation1ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
