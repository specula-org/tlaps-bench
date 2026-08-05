---- MODULE Ben_or83_proofs_Pres_Lemma12 ----
EXTENDS Ben_or83_proofs_Pres_Lemma12Scaffold
THEOREM Pres_Lemma12 ==
  ASSUME TypeOK, IndInv, [Next]_vars
  PROVE  Lemma12_CannotJumpRoundsWithoutQuorum'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
