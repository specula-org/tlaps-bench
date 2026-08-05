---- MODULE Ben_or83_proofs_Pres_L4_ST ----
EXTENDS Ben_or83_proofs_Pres_L4_STScaffold
THEOREM Pres_L4_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma4_MessagesNotFromFuture'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
