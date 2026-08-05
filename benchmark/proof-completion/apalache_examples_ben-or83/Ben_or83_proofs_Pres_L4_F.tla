---- MODULE Ben_or83_proofs_Pres_L4_F ----
EXTENDS Ben_or83_proofs_Pres_L4_FScaffold
THEOREM Pres_L4_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma4_MessagesNotFromFuture'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
