---- MODULE Ben_or83_proofs_Pres_L6_S1 ----
EXTENDS Ben_or83_proofs_Pres_L6_S1Scaffold
THEOREM Pres_L6_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma6_DecisionDefinesValue'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
