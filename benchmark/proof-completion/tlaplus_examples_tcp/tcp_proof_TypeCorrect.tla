---- MODULE tcp_proof_TypeCorrect ----
EXTENDS tcp_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Spec => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
