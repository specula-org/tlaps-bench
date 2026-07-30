---- MODULE LamportMutex_proofs_TypeCorrect ----
EXTENDS LamportMutex_proofs_TypeCorrectScaffold
USE DEF Clock
LEMMA TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
