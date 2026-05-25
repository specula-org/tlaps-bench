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
<1>1. Init => Inv
  BY CardinalityZero DEF Init, Inv
<1>2. Inv /\ [Next]_chosen => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_chosen
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    <3>1. PICK v \in Value : chosen' = {v}
      BY <2>1 DEF Next
    <3>2. chosen' \subseteq Value
      BY <3>1
    <3>3. IsFiniteSet(chosen') /\ Cardinality(chosen') = 1
      BY <3>1, CardinalityOne
    <3>4. QED
      BY <3>2, <3>3 DEF Inv
  <2>2. CASE UNCHANGED chosen
    BY <2>2 DEF Inv
  <2>3. QED
    BY <2>1, <2>2 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================