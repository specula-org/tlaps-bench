---- MODULE Ben_or83_proofs_Pres_Lemma1 ----
EXTENDS Ben_or83_proofs_Pres_Lemma1Scaffold
THEOREM Pres_Lemma1 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma1_DecisionRequiresLastQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
