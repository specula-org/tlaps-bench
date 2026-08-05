---- MODULE Ben_or83_proofs_Pres_L11_S1 ----
EXTENDS Ben_or83_proofs_Pres_L11_S1Scaffold
THEOREM Pres_L11_S1 ==
  ASSUME IndInv, NEW id \in CORRECT, Step1(id)
  PROVE  Lemma11_ValueOnQuorumLessRam'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
