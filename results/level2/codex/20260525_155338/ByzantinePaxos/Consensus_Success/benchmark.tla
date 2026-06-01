----------------------------- MODULE Consensus_Success ------------------------------

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

AXIOM EmptySetCardinality == IsFiniteSet({}) /\ Cardinality({}) = 0
AXIOM SingletonCardinality == 
          \A e : IsFiniteSet({e}) /\ (Cardinality({e}) = 1)

-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

THEOREM LiveSpec => Success
PROOF OBVIOUS
-----------------------------------------------------------------------------

=============================================================================

