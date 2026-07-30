---- MODULE Elevator_proof_TypeCorrect ----
EXTENDS Elevator_proof_TypeCorrectScaffold
THEOREM TypeCorrect == Spec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
