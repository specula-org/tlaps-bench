----------------------------- MODULE Consensus_Inv -----------------------------

EXTENDS Naturals, FiniteSets, TLAPS

LOCAL INSTANCE FiniteSetTheorems
-----------------------------------------------------------------------------
CONSTANTS Values 

VARIABLES chosen 

-----------------------------------------------------------------------------
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}
        
Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == Cardinality(chosen) <= 1

LEMMA EmptyInv ==
  Cardinality({}) <= 1
PROOF
  BY FS_EmptySet, SimpleArithmetic

LEMMA SingletonInv ==
  \A v : Cardinality({v}) <= 1
PROOF
  BY FS_Singleton, SimpleArithmetic

LEMMA InitInv ==
  Init => Inv
PROOF
  BY EmptyInv DEF Init, Inv

LEMMA NextInv ==
  Inv /\ [Next]_chosen => Inv'
PROOF
  <1>1. ASSUME Inv, [Next]_chosen
        PROVE Inv'
    <2>1. CASE Next
      <3>1. \E v \in Values : chosen' = {v}
        BY <2>1 DEF Next
      <3>2. PICK v \in Values : chosen' = {v}
        BY <3>1
      <3>3. Cardinality(chosen') <= 1
        BY <3>2, SingletonInv
      <3>4. QED
        BY <3>3 DEF Inv
    <2>2. CASE UNCHANGED chosen
      <3>1. chosen' = chosen
        BY <2>2
      <3>2. QED
        BY <1>1, <3>1 DEF Inv
    <2>3. QED
      BY <1>1, <2>1, <2>2
  <1>2. QED
    BY <1>1

THEOREM Spec => []Inv
PROOF
  BY InitInv, NextInv, PTL DEF Spec
=============================================================================
