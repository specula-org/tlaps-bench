----------------------------- MODULE Consensus_Inv -----------------------------

EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems
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

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
  <1>1. chosen = {} BY DEF Init
  <1>2. Cardinality({}) = 0 BY FS_EmptySet
  <1> QED BY <1>1, <1>2 DEF Inv

LEMMA InductiveStep == Inv /\ [Next]_chosen => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_chosen
               PROVE  Inv'
      OBVIOUS
  <1>1. CASE Next
    <2>1. PICK v \in Values : chosen' = {v}
      BY <1>1 DEF Next
    <2>2. Cardinality({v}) = 1
      BY FS_Singleton
    <2>3. Cardinality(chosen') = 1
      BY <2>1, <2>2
    <2> QED BY <2>3 DEF Inv
  <1>2. CASE UNCHANGED chosen
    BY <1>2 DEF Inv
  <1> QED BY <1>1, <1>2

THEOREM Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_chosen => Inv'
    BY InductiveStep
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec
=============================================================================
