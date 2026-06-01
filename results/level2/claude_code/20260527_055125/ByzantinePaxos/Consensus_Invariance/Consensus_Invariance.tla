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

LEMMA InitInv == Init => Inv
<1>1. SUFFICES ASSUME Init PROVE Inv
  OBVIOUS
<1>2. chosen = {}
  BY <1>1 DEF Init
<1>3. TypeOK
  <2>1. chosen \subseteq Value
    BY <1>2
  <2>2. IsFiniteSet(chosen)
    BY <1>2, EmptySetCardinality
  <2>3. QED
    BY <2>1, <2>2 DEF TypeOK
<1>4. Cardinality(chosen) \leq 1
  BY <1>2, EmptySetCardinality
<1>5. QED
  BY <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1>1. SUFFICES ASSUME Inv, Next \/ (vars' = vars) PROVE Inv'
  BY DEF vars
<1>2. CASE Next
  <2>1. PICK v \in Value : chosen' = {v}
    BY <1>2 DEF Next
  <2>2. TypeOK'
    <3>1. chosen' \subseteq Value
      BY <2>1
    <3>2. IsFiniteSet(chosen')
      BY <2>1, SingletonCardinality
    <3>3. QED
      BY <3>1, <3>2 DEF TypeOK
  <2>3. Cardinality(chosen') \leq 1
    BY <2>1, SingletonCardinality
  <2>4. QED
    BY <2>2, <2>3 DEF Inv
<1>3. CASE vars' = vars
  <2>1. chosen' = chosen
    BY <1>3 DEF vars
  <2>2. QED
    BY <2>1, <1>1 DEF Inv, TypeOK
<1>4. QED
  BY <1>1, <1>2, <1>3

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY NextInv
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

=============================================================================

