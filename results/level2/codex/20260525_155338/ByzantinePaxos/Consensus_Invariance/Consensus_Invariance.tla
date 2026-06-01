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

LEMMA EmptyTypeOK ==
  ASSUME chosen = {}
  PROVE  TypeOK
  PROOF
    <1>1. chosen \subseteq Value BY SMT
    <1>2. IsFiniteSet(chosen) BY EmptySetCardinality
    <1> QED BY <1>1, <1>2 DEF TypeOK

LEMMA EmptyInv == Init => Inv
  PROOF
    <1>1. ASSUME Init PROVE Inv
      <2>1. chosen = {} BY <1>1 DEF Init
      <2>2. TypeOK BY <2>1, EmptyTypeOK
      <2>3. Cardinality(chosen) <= 1 BY <2>1, EmptySetCardinality
      <2> QED BY <2>2, <2>3 DEF Inv
    <1> QED BY <1>1

LEMMA SingletonInv == 
  ASSUME NEW v \in Value,
         chosen' = {v}
  PROVE  Inv'
  PROOF
    <1>1. chosen' \subseteq Value BY SMT
    <1>2. IsFiniteSet(chosen') BY SingletonCardinality
    <1>3. Cardinality(chosen') <= 1 BY SingletonCardinality
    <1>4. TypeOK' BY <1>1, <1>2 DEF TypeOK
    <1> QED BY <1>3, <1>4 DEF Inv

LEMMA NextInv == Next => Inv'
  PROOF
    <1>1. ASSUME Next PROVE Inv'
      <2>1. \E v \in Value : chosen' = {v} BY <1>1 DEF Next
      <2>2. PICK v \in Value : chosen' = {v} BY <2>1
      <2> QED BY <2>2, SingletonInv
    <1> QED BY <1>1

LEMMA StutterInv == Inv /\ UNCHANGED vars => Inv'
  PROOF
    <1>1. ASSUME Inv, UNCHANGED vars PROVE Inv'
      <2>1. chosen' = chosen BY <1>1 DEF vars
      <2> QED BY <1>1, <2>1 DEF Inv, TypeOK
    <1> QED BY <1>1

LEMMA InductiveInvariance == Inv /\ [Next]_vars => Inv'
  PROOF
    <1>1. ASSUME Inv, [Next]_vars PROVE Inv'
      <2>1. CASE Next
        <3> QED BY <2>1, NextInv
      <2>2. CASE UNCHANGED vars
        <3> QED BY <1>1, <2>2, StutterInv
      <2> QED BY <1>1, <2>1, <2>2 DEF vars
    <1> QED BY <1>1

THEOREM Invariance == Spec => []Inv 
  PROOF
    <1>1. Init => Inv BY EmptyInv
    <1>2. Inv /\ [Next]_vars => Inv' BY InductiveInvariance
    <1> QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

=============================================================================
