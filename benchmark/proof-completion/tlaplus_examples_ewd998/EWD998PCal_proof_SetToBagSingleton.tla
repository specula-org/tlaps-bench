---- MODULE EWD998PCal_proof_SetToBagSingleton ----
EXTENDS EWD998PCal_proof_SetToBagSingletonScaffold
USE NAssumption
LEMMA SetToBagSingleton ==
  ASSUME NEW x
  PROVE  /\ DOMAIN SetToBag({x}) = {x}
         /\ SetToBag({x})[x] = 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
