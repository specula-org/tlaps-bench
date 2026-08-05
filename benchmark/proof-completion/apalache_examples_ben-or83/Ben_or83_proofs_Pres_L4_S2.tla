---- MODULE Ben_or83_proofs_Pres_L4_S2 ----
EXTENDS Ben_or83_proofs_Pres_L4_S2Scaffold
THEOREM Pres_L4_S2 ==
  ASSUME TypeOK, IndInv, NEW id \in CORRECT, Step2(id)
  PROVE  Lemma4_MessagesNotFromFuture'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
