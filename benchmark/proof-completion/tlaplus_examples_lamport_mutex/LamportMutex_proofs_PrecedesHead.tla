---- MODULE LamportMutex_proofs_PrecedesHead ----
EXTENDS LamportMutex_proofs_PrecedesHeadScaffold
USE DEF Clock
LEMMA PrecedesHead ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         s # << >>,
         Precedes(s,mt1,mt2), Head(s).type = mt2
  PROVE  ~ Contains(s,mt1)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
