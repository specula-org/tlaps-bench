---- MODULE Elevator_proof_ElevatorCallFields ----
EXTENDS Elevator_proof_ElevatorCallFieldsScaffold
LEMMA ElevatorCallFields ==
  ASSUME NEW c \in ElevatorCall
  PROVE  /\ c.floor \in Floor
         /\ c.direction \in Direction
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
