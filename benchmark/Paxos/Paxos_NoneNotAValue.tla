---- MODULE Paxos_NoneNotAValue ----
EXTENDS FiniteSets, Integers, Naturals, TLAPS, TLC
(* ---- Content from module Consensus ---- *)
(***************************************************************************)
(* This is a trivial specification of consensus.  It asserts that the      *)
(* variable `chosen', which represents the set of values that someone      *)
(* might think has been chosen is initially empty and can be changed only  *)
(* by adding a single element to it.                                       *)
(***************************************************************************)
-----------------------------------------------------------------------------
CONSTANTS Values \* the set of all values that can be chosen

VARIABLES chosen \* the set of all values that have been chosen

TypeOK ==
    /\ chosen \subseteq Values
    /\ IsFiniteSet(chosen)
-----------------------------------------------------------------------------
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}
        
Spec == Init /\ [][Next]_chosen
-----------------------------------------------------------------------------
Inv == Cardinality(chosen) <= 1
    \* /\ TypeOK
    \* /\ Cardinality(chosen) <= 1

THEOREM Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv
  (*
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2> QED
    BY DEF Init, Inv
  *)
  
<1>2. Inv /\ [Next]_chosen => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_chosen
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    BY <2>1 DEF Inv, Next
  <2>2. CASE UNCHANGED chosen
    BY <2>2 DEF Inv, Next
  <2>3. QED
    BY <2>1, <2>2
  
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

(* 
Specification and Verification of Basic Paxos.

See http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple
*)
-----------------------------------------------------------------------------
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
  PROOF OMITTED

Ballots == Nat

None == CHOOSE v : v \notin Values

LEMMA NoneNotAValue == None \notin Values
PROOF OBVIOUS

========================================