---- MODULE EWD998PCal_proof_BagRemoveOfMsg ----
EXTENDS EWD998PCal_proof_BagRemoveOfMsgScaffold
USE NAssumption
LEMMA BagRemoveOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW x
  PROVE  BagRemove(B, x) \in BagOf(Msg)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
