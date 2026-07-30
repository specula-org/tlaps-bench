---- MODULE LamportMutex_proofs_PrecedesInTail ----
EXTENDS LamportMutex_proofs_PrecedesInTailScaffold
USE DEF Clock
LEMMA PrecedesInTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, mt1 # mt2,
         Head(s).type = mt1 \/ Head(s).type \notin {mt1, mt2},
         Precedes(Tail(s), mt1, mt2)
  PROVE  Precedes(s, mt1, mt2)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
