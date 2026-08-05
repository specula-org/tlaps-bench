---- MODULE Ben_or83_proofs_Pres_L1_S1 ----
EXTENDS Ben_or83_proofs_Pres_L1_S1Scaffold
THEOREM Pres_L1_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
