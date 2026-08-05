---------------------------- MODULE Elevator_proof_TypeCorrectDefs ----------------------------

EXTENDS Elevator, TLAPS

ASSUME ElevatorFloorDisjoint == Floor \cap Elevator = {}

=============================================================================
