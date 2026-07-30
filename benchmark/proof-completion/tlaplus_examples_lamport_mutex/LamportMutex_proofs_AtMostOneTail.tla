---- MODULE LamportMutex_proofs_AtMostOneTail ----
EXTENDS LamportMutex_proofs_AtMostOneTailScaffold
USE DEF Clock
LEMMA AtMostOneTail ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         s # << >>, AtMostOne(s, mtype)
  PROVE  AtMostOne(Tail(s), mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
