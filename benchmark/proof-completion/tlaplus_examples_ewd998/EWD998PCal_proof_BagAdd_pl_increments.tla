---- MODULE EWD998PCal_proof_BagAdd_pl_increments ----
EXTENDS EWD998PCal_proof_BagAdd_pl_incrementsScaffold
USE NAssumption
LEMMA BagAdd_pl_increments ==
  ASSUME NEW B
  PROVE  PlCount(BagAdd(B, [type |-> "pl"])) = PlCount(B) + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
