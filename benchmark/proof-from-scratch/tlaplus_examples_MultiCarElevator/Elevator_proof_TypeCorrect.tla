---- MODULE Elevator_proof_TypeCorrect ----
EXTENDS Elevator_proof_TypeCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TypeCorrect == Spec => []TypeInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
