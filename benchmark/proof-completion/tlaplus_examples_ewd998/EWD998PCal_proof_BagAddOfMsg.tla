---- MODULE EWD998PCal_proof_BagAddOfMsg ----
EXTENDS EWD998PCal_proof_BagAddOfMsgScaffold
USE NAssumption
LEMMA BagAddOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW m \in Msg
  PROVE  BagAdd(B, m) \in BagOf(Msg)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
