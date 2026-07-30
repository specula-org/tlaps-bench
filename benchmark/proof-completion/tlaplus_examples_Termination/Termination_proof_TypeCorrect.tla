---- MODULE Termination_proof_TypeCorrect ----
EXTENDS Termination_proof_TypeCorrectScaffold
LEMMA TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
