----------------------------- MODULE Consensus_Invariance ------------------------------

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

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv 
PROOF OBVIOUS

-----------------------------------------------------------------------------

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

=============================================================================
