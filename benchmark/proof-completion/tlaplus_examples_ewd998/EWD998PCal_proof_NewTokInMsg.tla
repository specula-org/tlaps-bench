---- MODULE EWD998PCal_proof_NewTokInMsg ----
EXTENDS EWD998PCal_proof_NewTokInMsgScaffold
USE NAssumption
LEMMA NewTokInMsg ==
  ASSUME NEW q \in Int, NEW c \in ColorSet
  PROVE  [type |-> "tok", q |-> q, color |-> c] \in Msg
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
