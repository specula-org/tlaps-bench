------------------------- MODULE Termination_proof_Invariant3 -------------------------
EXTENDS Termination, TLAPS

(***************************************************************************)
(* This module contains a proof of the safety properties of the            *)
(* termination detection algorithm that is checked by TLAPS.               *)
(*                                                                         *)
(* We start by proving type correctness.                                   *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* We prove that Inv1 is an inductive invariant,                           *) 
(* relative to type correctness.                                           *)
(***************************************************************************)
LEMMA Invariant1 == Spec => []Inv1
PROOF OMITTED

(***************************************************************************)
(* Now, prove invariance of Inv2 based on the two previous invariants.     *)
(***************************************************************************)
LEMMA Invariant2 == Spec => []Inv2
PROOF OMITTED

(***************************************************************************)
(* Proving that Inv3 is an invariant is easy.                              *)
(***************************************************************************)
LEMMA Invariant3 == Spec => []Inv3
PROOF OBVIOUS

(***************************************************************************)
(* Finally, infer that the algorithm satisfies the safety condition.       *)
(***************************************************************************)

=============================================================================
