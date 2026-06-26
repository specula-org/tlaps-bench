----------------------------- MODULE Consensus ------------------------------ 
EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value 

VARIABLE chosen

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen 
-----------------------------------------------------------------------------

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv
  PROOF OMITTED

-----------------------------------------------------------------------------

Success == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)  

ASSUME ValuesNonempty == Value # {}

THEOREM LivenessTheorem == LiveSpec =>  Success
  PROOF OMITTED

=============================================================================
