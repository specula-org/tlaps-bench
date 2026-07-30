---- MODULE Simple_proof_TypeCorrect ----
EXTENDS Simple_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
