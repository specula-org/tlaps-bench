----------------------------- MODULE Consensus_Invariance ------------------------------
EXTENDS Sets, TLAPS
-----------------------------------------------------------------------------
CONSTANT Value  
VARIABLE chosen 
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
LEMMA InitInv == Init => Inv
  BY CardinalityZero DEF Init, Inv

LEMMA NextInv == Inv /\ [Next]_chosen => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_chosen
               PROVE  Inv'
    OBVIOUS
  <1>1. CASE Next
    <2>1. PICK v \in Value : chosen' = {v}
      BY <1>1 DEF Next
    <2>2. chosen' \subseteq Value
      BY <2>1
    <2>3. IsFiniteSet(chosen')
      BY <2>1, CardinalityOne
    <2>4. Cardinality(chosen') \leq 1
      BY <2>1, CardinalityOne
    <2>5. QED
      BY <2>2, <2>3, <2>4 DEF Inv
  <1>2. CASE UNCHANGED chosen
    BY <1>2 DEF Inv
  <1>3. QED
    BY <1>1, <1>2 DEF Next
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
PROOF
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_chosen => Inv'
    BY NextInv
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec
=============================================================================