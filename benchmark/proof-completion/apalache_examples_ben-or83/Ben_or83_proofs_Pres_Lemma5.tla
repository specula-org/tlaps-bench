---- MODULE Ben_or83_proofs_Pres_Lemma5 ----
EXTENDS Ben_or83_proofs_Pres_Lemma5Scaffold
THEOREM Pres_Lemma5 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma5_RoundNeedsSentMessages'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
