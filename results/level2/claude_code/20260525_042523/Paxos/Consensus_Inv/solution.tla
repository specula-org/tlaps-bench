----------------------------- MODULE Consensus_Inv -----------------------------
(***************************************************************************)
(* This is a trivial specification of consensus.  It asserts that the      *)
(* variable `chosen', which represents the set of values that someone      *)
(* might think has been chosen is initially empty and can be changed only  *)
(* by adding a single element to it.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLAPS
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

(***************************************************************************)
(* Scaffolding for the inductive-invariant proof.  We instantiate          *)
(* FiniteSetTheorems to obtain the cardinality facts for the empty set and *)
(* singletons, then bridge its (instantiated) Cardinality operator to the  *)
(* local one and prove the two cardinality lemmas we need.                 *)
(***************************************************************************)
FT == INSTANCE FiniteSetTheorems

LEMMA EquivCard == \A S : FT!Cardinality(S) = Cardinality(S)
  BY DEF Cardinality, FT!Cardinality

LEMMA CardEmpty == Cardinality({}) = 0
  BY FT!FS_EmptySet, EquivCard

LEMMA CardSingleton == \A v : Cardinality({v}) = 1
  BY FT!FS_Singleton, EquivCard

(***************************************************************************)
(* The two halves of the standard inductive-invariant argument:           *)
(* initiation and consecution.                                            *)
(***************************************************************************)
LEMMA InitInv == Init => Inv
  BY CardEmpty DEF Init, Inv

LEMMA NextInv ==
  ASSUME Inv, [Next]_chosen
  PROVE  Inv'
  <1>1. CASE Next
    <2>1. PICK v \in Values : chosen' = {v}
      BY <1>1 DEF Next
    <2>2. Cardinality(chosen') = 1
      BY <2>1, CardSingleton
    <2> QED
      BY <2>2 DEF Inv
  <1>2. CASE chosen' = chosen
    BY <1>2 DEF Inv
  <1> QED
    BY <1>1, <1>2 DEF Next

THEOREM Spec => []Inv
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_chosen => Inv'
  BY NextInv
<1> QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 13:47:23 CST 2019 by hengxin
\* Last modified Tue Jul 16 11:26:27 CST 2019 by hengxin
\* Last modified Wed Nov 21 11:35:33 PST 2012 by lamport
\* Created Mon Nov 19 15:19:09 PST 2012 by lamport
