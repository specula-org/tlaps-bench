---- MODULE CigaretteSmokers_proof_TypeCorrect ----
EXTENDS CigaretteSmokers_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
