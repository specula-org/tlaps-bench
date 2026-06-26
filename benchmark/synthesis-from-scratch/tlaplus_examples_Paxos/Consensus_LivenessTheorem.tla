----------------------------- MODULE Consensus_LivenessTheorem ------------------------------
EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value 

VARIABLE chosen

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen 
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

Success == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)  

ASSUME ValuesNonempty == Value # {}

THEOREM LivenessTheorem == LiveSpec =>  Success
PROOF OBVIOUS
=============================================================================
