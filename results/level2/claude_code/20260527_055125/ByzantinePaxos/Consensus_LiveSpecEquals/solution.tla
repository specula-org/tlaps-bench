----------------------------- MODULE Consensus_LiveSpecEquals ------------------------------

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

ASSUME ValueNonempty == Value # {}

-----------------------------------------------------------------------------

LEMMA EnabledEquiv == (ENABLED <<Next>>_vars) <=> (chosen = {})
BY ExpandENABLED, ValueNonempty DEF Next, vars

THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
<1>1. [](~(ENABLED <<Next>>_vars) <=> (chosen # {}))
  <2>1. (~(ENABLED <<Next>>_vars)) <=> (chosen # {})
    BY EnabledEquiv
  <2>2. QED
    BY <2>1, PTL
<1>2. QED
  BY <1>1, PTL DEF LiveSpec
=============================================================================

