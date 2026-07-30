---- MODULE LamportMutex_proofs_PrecedesSend ----
EXTENDS LamportMutex_proofs_PrecedesSendScaffold
USE DEF Clock
LEMMA PrecedesSend ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         NEW m \in Message, m.type # mt1
  PROVE  Precedes(Append(s,m), mt1, mt2) <=> Precedes(s, mt1, mt2)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
