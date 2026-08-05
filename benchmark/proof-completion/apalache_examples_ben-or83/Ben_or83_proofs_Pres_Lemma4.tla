---- MODULE Ben_or83_proofs_Pres_Lemma4 ----
EXTENDS Ben_or83_proofs_Pres_Lemma4Scaffold
THEOREM Pres_Lemma4 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma4_MessagesNotFromFuture'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
