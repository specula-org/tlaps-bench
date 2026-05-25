----------------------------- MODULE Consensus_Invariance ------------------------------
EXTENDS Sets, TLAPS
-----------------------------------------------------------------------------
CONSTANT Value  \* the set of values that can be chosen
VARIABLE chosen \* the set of values that have been chosen
-----------------------------------------------------------------------------
Init == chosen = {}

Next == 
    /\ chosen = {}
    /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == 
    /\ chosen \subseteq Value
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) \leq 1
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
PROOF OBVIOUS
=============================================================================