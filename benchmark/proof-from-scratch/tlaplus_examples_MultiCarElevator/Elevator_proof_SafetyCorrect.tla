---- MODULE Elevator_proof_SafetyCorrect ----
EXTENDS Elevator_proof_SafetyCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM SafetyCorrect == Spec => []SafetyInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
