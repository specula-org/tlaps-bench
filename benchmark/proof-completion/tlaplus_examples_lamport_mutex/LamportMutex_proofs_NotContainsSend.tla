---- MODULE LamportMutex_proofs_NotContainsSend ----
EXTENDS LamportMutex_proofs_NotContainsSendScaffold
USE DEF Clock
LEMMA NotContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s, mtype), NEW m \in Message
  PROVE  /\ AtMostOne(Append(s,m), mtype)
         /\ m.type # mtype => ~ Contains(Append(s,m), mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
