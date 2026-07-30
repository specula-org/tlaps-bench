---- MODULE LamportMutex_proofs_AtMostOneSend ----
EXTENDS LamportMutex_proofs_AtMostOneSendScaffold
USE DEF Clock
LEMMA AtMostOneSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, AtMostOne(s, mtype), 
         NEW m \in Message, m.type # mtype
  PROVE  AtMostOne(Append(s,m), mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
