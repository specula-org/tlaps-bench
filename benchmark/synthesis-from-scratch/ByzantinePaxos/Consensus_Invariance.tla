----------------------------- MODULE Consensus_Invariance ------------------------------

EXTENDS Naturals, FiniteSets, TLAPS

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

AXIOM EmptySetCardinality == IsFiniteSet({}) /\ Cardinality({}) = 0
AXIOM SingletonCardinality == 
          \A e : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)

THEOREM Invariance == Spec => []Inv 
PROOF OBVIOUS

-----------------------------------------------------------------------------

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

=============================================================================

