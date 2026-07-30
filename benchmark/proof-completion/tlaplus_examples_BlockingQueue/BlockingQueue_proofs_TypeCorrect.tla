---- MODULE BlockingQueue_proofs_TypeCorrect ----
EXTENDS BlockingQueue_proofs_TypeCorrectScaffold
LEMMA TypeCorrect == Spec => []TypeInv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
