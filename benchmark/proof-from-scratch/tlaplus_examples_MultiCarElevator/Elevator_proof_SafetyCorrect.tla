---------------------------- MODULE Elevator_proof_SafetyCorrect ----------------------------

EXTENDS Elevator, TLAPS

ASSUME ElevatorFloorDisjoint == Floor \cap Elevator = {}

THEOREM SafetyCorrect == Spec => []SafetyInvariant
PROOF OBVIOUS

=============================================================================
