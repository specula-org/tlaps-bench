------------------------- MODULE Termination_proof_Invariant2Scaffold -------------------------
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
=============================================================================
