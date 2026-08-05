---- MODULE Ben_or83_proofs_Pres_L8_S1 ----
EXTENDS Ben_or83_proofs_Pres_L8_S1Scaffold
THEOREM Pres_L8_S1 ==
  ASSUME TypeOK, IndInv, NEW id0 \in CORRECT, Step1(id0)
  PROVE  Lemma8_Q2RequiresNoQuorumFaster'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
