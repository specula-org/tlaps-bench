---------------------------- MODULE Elevator_proof_TypeCorrect ----------------------------

EXTENDS Elevator, TLAPS

ASSUME ElevatorFloorDisjoint == Floor \cap Elevator = {}

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

=============================================================================
