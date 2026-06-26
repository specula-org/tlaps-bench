----------------------------- MODULE Consensus_LiveSpecEquals ------------------------------

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

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
PROOF OBVIOUS

=============================================================================
