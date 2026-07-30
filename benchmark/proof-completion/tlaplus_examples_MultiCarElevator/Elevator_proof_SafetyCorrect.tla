---- MODULE Elevator_proof_SafetyCorrect ----
EXTENDS Elevator_proof_SafetyCorrectScaffold
THEOREM SafetyCorrect == Spec => []SafetyInvariant
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
