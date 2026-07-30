---- MODULE LamportMutex_proofs_NotContainsPrecedes ----
EXTENDS LamportMutex_proofs_NotContainsPrecedesScaffold
USE DEF Clock
LEMMA NotContainsPrecedes ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, ~ Contains(s, mt2)
  PROVE  /\ Precedes(s, mt1, mt2)
         /\ Precedes(s, mt2, mt1)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
