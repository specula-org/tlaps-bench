---------------------------- MODULE Elevator_proof_SafetyCorrectDefs ----------------------------

EXTENDS Elevator, TLAPS

ASSUME ElevatorFloorDisjoint == Floor \cap Elevator = {}

=============================================================================
