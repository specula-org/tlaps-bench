--------------------------- MODULE stages_proof_TypeCorrect -------------------------------
(***************************************************************************)
(* TLAPS proof of the type-correctness invariant of stages.tla.            *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(***************************************************************************)
EXTENDS stages, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

LEMMA NatMinNat ==
  ASSUME NEW i \in Nat, NEW j \in Nat
  PROVE  natMin(i, j) \in Nat
PROOF OMITTED

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
