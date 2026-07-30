---- MODULE EWD998PCal_proof_BagRemove_pl_decrements ----
EXTENDS EWD998PCal_proof_BagRemove_pl_decrementsScaffold
USE NAssumption
LEMMA BagRemove_pl_decrements ==
  ASSUME NEW B, [type |-> "pl"] \in DOMAIN B,
         B[[type |-> "pl"]] \in Nat \ {0}
  PROVE  PlCount(BagRemove(B, [type |-> "pl"])) = PlCount(B) - 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
