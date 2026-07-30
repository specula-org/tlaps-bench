---- MODULE LamportMutex_proofs_BroadcastType ----
EXTENDS LamportMutex_proofs_BroadcastTypeScaffold
USE DEF Clock
LEMMA BroadcastType ==
  ASSUME network \in [Proc -> [Proc -> Seq(Message)]],
         NEW s \in Proc, NEW m \in Message
  PROVE  Broadcast(s,m) \in [Proc -> Seq(Message)]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
