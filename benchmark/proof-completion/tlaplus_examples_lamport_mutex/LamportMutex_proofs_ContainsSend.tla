---- MODULE LamportMutex_proofs_ContainsSend ----
EXTENDS LamportMutex_proofs_ContainsSendScaffold
USE DEF Clock
LEMMA ContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, NEW m \in Message
  PROVE  Contains(Append(s,m), mtype) <=> m.type = mtype \/ Contains(s, mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
