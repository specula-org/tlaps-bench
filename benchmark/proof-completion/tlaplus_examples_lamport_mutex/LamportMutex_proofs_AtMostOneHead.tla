---- MODULE LamportMutex_proofs_AtMostOneHead ----
EXTENDS LamportMutex_proofs_AtMostOneHeadScaffold
USE DEF Clock
LEMMA AtMostOneHead ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         AtMostOne(s,mtype), s # << >>, Head(s).type = mtype
  PROVE  ~ Contains(Tail(s), mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
