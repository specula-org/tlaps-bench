---- MODULE LamportMutex_proofs_PrecedesTail ----
EXTENDS LamportMutex_proofs_PrecedesTailScaffold
USE DEF Clock
LEMMA PrecedesTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, Precedes(s, mt1, mt2)
  PROVE  Precedes(Tail(s), mt1, mt2)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
