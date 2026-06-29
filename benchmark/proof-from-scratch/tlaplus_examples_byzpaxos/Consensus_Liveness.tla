----------------------------- MODULE Consensus_Liveness ------------------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANT Value  

VARIABLE chosen

vars == << chosen >>

Init == 
        /\ chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value:
             chosen' = {v}

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

THEOREM Liveness == LiveSpec => Success
PROOF OBVIOUS

-----------------------------------------------------------------------------

=============================================================================
