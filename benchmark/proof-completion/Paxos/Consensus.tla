----------------------------- MODULE Consensus -----------------------------

EXTENDS Naturals, FiniteSets, TLAPS
-----------------------------------------------------------------------------
CONSTANTS Values 

VARIABLES chosen 

TypeOK ==
    /\ chosen \subseteq Values
    /\ IsFiniteSet(chosen)
-----------------------------------------------------------------------------
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}
        
Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == Cardinality(chosen) <= 1

THEOREM Spec => []Inv
  PROOF OMITTED

=============================================================================

