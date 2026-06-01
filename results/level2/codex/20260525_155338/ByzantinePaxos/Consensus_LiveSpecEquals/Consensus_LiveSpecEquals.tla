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

LEMMA EnabledNext ==
        (ENABLED <<Next>>_vars) <=> (chosen = {})
  PROOF BY ValueNonempty, ExpandENABLED, AutoUSE DEF Next, vars

THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
  PROOF
    <1>1. WF_vars(Next) <=> ([]<>(~ ENABLED <<Next>>_vars) \/ []<><<Next>>_vars)
      BY PTL
    <1>2. ~ ENABLED <<Next>>_vars <=> chosen # {}
      BY EnabledNext
    <1>3. ([]<>(~ ENABLED <<Next>>_vars) \/ []<><<Next>>_vars)
          <=> ([]<><<Next>>_vars \/ []<>(chosen # {}))
      BY <1>2, PTL
    <1>4. QED
      BY <1>1, <1>3 DEF LiveSpec
=============================================================================
