------------------------- MODULE Termination_proof_Invariant1Scaffold -------------------------
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
=============================================================================
