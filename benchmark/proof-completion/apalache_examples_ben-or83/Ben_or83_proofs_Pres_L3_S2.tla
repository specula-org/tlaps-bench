---- MODULE Ben_or83_proofs_Pres_L3_S2 ----
EXTENDS Ben_or83_proofs_Pres_L3_S2Scaffold
THEOREM Pres_L3_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma3_NoEquivocation2ByCorrect'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
