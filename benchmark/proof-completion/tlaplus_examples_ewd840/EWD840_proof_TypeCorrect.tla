---- MODULE EWD840_proof_TypeCorrect ----
EXTENDS EWD840_proof_TypeCorrectScaffold
USE NAssumption
LEMMA TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
