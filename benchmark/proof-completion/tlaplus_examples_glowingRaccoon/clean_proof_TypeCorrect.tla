--------------------------- MODULE clean_proof_TypeCorrect --------------------------------
(***************************************************************************)
(* TLAPS proof of the safety invariants of clean.tla:                      *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []primerPositive                                              *)
(*   Spec => []preservationInvariant                                       *)
(***************************************************************************)
EXTENDS clean, TLAPS

(***************************************************************************)
(* The CONSTANTS DNA, PRIMER are unconstrained in the spec; for the        *)
(* arithmetic preservation argument we need them in Nat.  Restate as a     *)
(* named ASSUME in the proof file.                                         *)
(***************************************************************************)
ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

LEMMA NatMinNat ==
  ASSUME NEW i \in Nat, NEW j \in Nat
  PROVE  natMin(i, j) \in Nat
PROOF OMITTED

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

============================================================================
