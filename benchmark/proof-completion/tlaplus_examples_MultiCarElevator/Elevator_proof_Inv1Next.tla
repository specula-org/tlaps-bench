---- MODULE Elevator_proof_Inv1Next ----
EXTENDS Elevator_proof_Inv1NextScaffold
LEMMA Inv1Next == Inv1 /\ [Next]_Vars => Inv1'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
