---- MODULE Ben_or83_proofs_Pres_Lemma3 ----
EXTENDS Ben_or83_proofs_Pres_Lemma3Scaffold
THEOREM Pres_Lemma3 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma3_NoEquivocation2ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
