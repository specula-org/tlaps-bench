------------------------- MODULE Termination_proof_TypeCorrect -------------------------
EXTENDS Termination, TLAPS

(***************************************************************************)
(* This module contains a proof of the safety properties of the            *)
(* termination detection algorithm that is checked by TLAPS.               *)
(*                                                                         *)
(* We start by proving type correctness.                                   *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

(***************************************************************************)
(* We prove that Inv1 is an inductive invariant,                           *) 
(* relative to type correctness.                                           *)
(***************************************************************************)

(***************************************************************************)
(* Now, prove invariance of Inv2 based on the two previous invariants.     *)
(***************************************************************************)

(***************************************************************************)
(* Proving that Inv3 is an invariant is easy.                              *)
(***************************************************************************)

(***************************************************************************)
(* Finally, infer that the algorithm satisfies the safety condition.       *)
(***************************************************************************)

=============================================================================
