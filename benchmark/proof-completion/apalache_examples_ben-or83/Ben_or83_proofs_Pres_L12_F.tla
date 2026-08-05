---- MODULE Ben_or83_proofs_Pres_L12_F ----
EXTENDS Ben_or83_proofs_Pres_L12_FScaffold
THEOREM Pres_L12_F ==
  ASSUME TypeOK, IndInv, FaultyStep
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
