----------------------------- MODULE Consensus ------------------------------ 

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

LEMMA InductiveInvariance ==
           Inv /\ [Next]_vars => Inv'
  PROOF OMITTED

THEOREM Invariance == Spec => []Inv 
  PROOF OMITTED

-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

LEMMA EnabledDef == (ENABLED <<Next>>_vars) <=> (chosen = {})
  PROOF OMITTED

THEOREM Liveness == LiveSpec => Success
  PROOF OMITTED

-----------------------------------------------------------------------------

THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
  PROOF OMITTED

=============================================================================
