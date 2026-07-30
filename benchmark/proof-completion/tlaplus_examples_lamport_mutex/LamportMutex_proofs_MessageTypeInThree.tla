---- MODULE LamportMutex_proofs_MessageTypeInThree ----
EXTENDS LamportMutex_proofs_MessageTypeInThreeScaffold
USE DEF Clock
LEMMA MessageTypeInThree ==
  ASSUME NEW m \in Message
  PROVE  m.type \in {"req", "ack", "rel"}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
