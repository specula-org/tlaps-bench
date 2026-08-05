---- MODULE Ben_or83_proofs_Pres_L5_ST ----
EXTENDS Ben_or83_proofs_Pres_L5_STScaffold
THEOREM Pres_L5_ST ==
  ASSUME IndInv, UNCHANGED vars
  PROVE  Lemma5_RoundNeedsSentMessages'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
