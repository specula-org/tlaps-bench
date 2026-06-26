----------------------------- MODULE Consensus_LivenessTheorem ------------------------------
EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value 
  (*************************************************************************)
  (* The set of all values that can be chosen.                             *)
  (*************************************************************************)
  
VARIABLE chosen
  (*************************************************************************)
  (* The set of all values that have been chosen.                          *)
  (*************************************************************************)
  
(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

(***************************************************************************)
(* The initial predicate and next-state relation.                          *)
(***************************************************************************)
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

(***************************************************************************)
(* The complete spec.                                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_chosen 
(***************************************************************************)
(* Safety: At most one value is chosen.                                    *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv
PROOF OMITTED

(***************************************************************************)
(* Liveness: A value is eventually chosen.                                 *)
(***************************************************************************)
Success == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)  

ASSUME ValuesNonempty == Value # {}

THEOREM LivenessTheorem == LiveSpec =>  Success
PROOF OBVIOUS
=============================================================================
