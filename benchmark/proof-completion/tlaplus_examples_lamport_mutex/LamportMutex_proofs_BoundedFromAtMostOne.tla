---- MODULE LamportMutex_proofs_BoundedFromAtMostOne ----
EXTENDS LamportMutex_proofs_BoundedFromAtMostOneScaffold
USE DEF Clock
LEMMA BoundedFromAtMostOne ==
  ASSUME NEW s \in Seq(Message),
         AtMostOne(s, "req"),
         AtMostOne(s, "ack"),
         AtMostOne(s, "rel")
  PROVE  Len(s) <= 3
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
