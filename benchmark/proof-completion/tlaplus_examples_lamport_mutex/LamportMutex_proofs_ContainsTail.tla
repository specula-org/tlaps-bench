---- MODULE LamportMutex_proofs_ContainsTail ----
EXTENDS LamportMutex_proofs_ContainsTailScaffold
USE DEF Clock
LEMMA ContainsTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mtype, AtMostOne(s, mtype)
  PROVE  Contains(Tail(s), mtype) <=> Contains(s, mtype) /\ Head(s).type # mtype
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
