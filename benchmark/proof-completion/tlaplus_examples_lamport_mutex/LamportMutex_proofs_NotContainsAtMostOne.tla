---- MODULE LamportMutex_proofs_NotContainsAtMostOne ----
EXTENDS LamportMutex_proofs_NotContainsAtMostOneScaffold
USE DEF Clock
LEMMA NotContainsAtMostOne ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s,mtype)
  PROVE  AtMostOne(s, mtype)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
