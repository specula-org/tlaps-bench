----------------------------- MODULE Consensus_Success ------------------------------

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
Success == <>(chosen # {})

ASSUME ValueNonempty == Value # {}

Start == chosen = {}
Done == chosen # {}

LEMMA InitImpliesStart ==
        Init => Start
PROOF BY DEF Init, Start

LEMMA NextImpliesSuccessPrime ==
        Next => Done'
PROOF BY DEF Next, Done

LEMMA NextImpliesStartOrDonePrime ==
        Start /\ [Next]_vars => (Start' \/ Done')
PROOF
  <1>1. SUFFICES ASSUME Start,
                         [Next]_vars
                  PROVE  Start' \/ Done'
    OBVIOUS
  <1>2. CASE Next
    <2>1. Done'
      BY <1>2, NextImpliesSuccessPrime
    <2>2. QED
      BY <2>1
  <1>3. CASE UNCHANGED vars
    <2>1. Start'
      BY <1>1, <1>3 DEF Start, vars
    <2>2. QED
      BY <2>1
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF vars

LEMMA NextActionImpliesSuccessPrime ==
        Start /\ <<Next /\ Next>>_vars => Done'
PROOF
  <1>1. SUFFICES ASSUME Start,
                         <<Next /\ Next>>_vars
                  PROVE  Done'
    OBVIOUS
  <1>2. Next
    BY <1>1 DEF vars
  <1>3. QED
    BY <1>2, NextImpliesSuccessPrime

LEMMA StartImpliesEnabledNext ==
        Start => ENABLED <<Next>>_vars
PROOF
  <1>1. SUFFICES ASSUME Start
                  PROVE  ENABLED <<Next>>_vars
    OBVIOUS
  <1>2. \E v : v \in Value
    BY ValueNonempty
  <1>3. QED
    BY <1>1, <1>2, ExpandENABLED DEF Start, Next, vars

LEMMA StartLeadsToDone ==
        [][Next]_vars /\ WF_vars(Next) => (Start ~> Done)
PROOF
  <1>1. Start /\ [Next]_vars => (Start' \/ Done')
    BY NextImpliesStartOrDonePrime
  <1>2. Start /\ <<Next /\ Next>>_vars => Done'
    BY NextActionImpliesSuccessPrime
  <1>3. Start => ENABLED <<Next>>_vars
    BY StartImpliesEnabledNext
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL

THEOREM LiveSpec => Success
PROOF
  <1>1. SUFFICES ASSUME LiveSpec
                  PROVE  Success
    OBVIOUS
  <1>2. Init
    BY <1>1 DEF LiveSpec, Spec
  <1>3. [][Next]_vars /\ WF_vars(Next)
    BY <1>1 DEF LiveSpec, Spec
  <1>4. Start ~> Done
    BY <1>3, StartLeadsToDone
  <1>5. Start
    BY <1>2, InitImpliesStart
  <1>6. QED
    BY <1>4, <1>5, PTL DEF Success, Start, Done
-----------------------------------------------------------------------------

=============================================================================
