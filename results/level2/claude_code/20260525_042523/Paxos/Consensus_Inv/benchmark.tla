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

THEOREM Spec => []Inv
PROOF OBVIOUS
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 13:47:23 CST 2019 by hengxin
\* Last modified Tue Jul 16 11:26:27 CST 2019 by hengxin
\* Last modified Wed Nov 21 11:35:33 PST 2012 by lamport
\* Created Mon Nov 19 15:19:09 PST 2012 by lamport
