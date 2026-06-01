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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Scaffolding for the liveness proof.                                     *)
(*                                                                         *)
(* The argument is a weak-fairness liveness proof.  Since `Next' requires  *)
(* chosen = {} and produces a nonempty `chosen', the WF1-style reasoning   *)
(* is carried out directly via the PTL backend: if `chosen' stayed empty   *)
(* forever then `Next' would be perpetually enabled, so weak fairness      *)
(* would force a `Next' step, which makes `chosen' nonempty -- a           *)
(* contradiction.                                                          *)
(***************************************************************************)

(* From any empty state, a <<Next>>_vars step is enabled (uses Value # {}).*)
LEMMA EnabledNext == (chosen = {}) => ENABLED <<Next>>_vars
  BY ValueNonempty, ExpandENABLED DEF Next, vars

(* If `chosen' is empty now and at the next state, no <<Next>>_vars step    *)
(* occurred, because `Next' makes `chosen' a nonempty singleton.            *)
LEMMA EmptyNoNext == ASSUME (chosen = {}), (chosen = {})' PROVE ~ <<Next>>_vars
  BY DEF Next, vars

(* Bridge from the temporal negation atom to the goal's set-inequality.     *)
LEMMA NotAlwaysEmpty == ~[](chosen = {}) => <>(chosen # {})
  <1>1. (chosen # {}) <=> ~(chosen = {})  OBVIOUS
  <1> QED BY ONLY <1>1, PTL

THEOREM LiveSpec => Success
<1> SUFFICES ASSUME LiveSpec PROVE <>(chosen # {})
    BY DEF Success
<1>1. [][Next]_vars   BY DEF LiveSpec, Spec
<1>2. WF_vars(Next)   BY DEF LiveSpec
<1>10. ~ [](chosen = {})
  <2> SUFFICES ASSUME [](chosen = {}) PROVE FALSE
      OBVIOUS
  <2>3. []ENABLED <<Next>>_vars
      BY EnabledNext, PTL
  <2>4. []<><<Next>>_vars
      BY <1>2, <2>3, PTL
  <2>5. [](~ <<Next>>_vars)
    <3>1. [](chosen = {}) => []((chosen = {}) /\ (chosen = {})')  BY PTL
    <3> QED BY <3>1, EmptyNoNext, PTL
  <2> QED BY <2>4, <2>5, PTL
<1> QED BY <1>10, NotAlwaysEmpty
-----------------------------------------------------------------------------

=============================================================================

