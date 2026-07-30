---------------------------- MODULE EWD840_proof_InvariantScaffold ----------------------------
(***************************************************************************)
(* This module contains the proof of the safety properties of Dijkstra's   *)
(* termination detection algorithm. Checking the proof requires TLAPS to   *)
(* be installed.                                                           *)
(***************************************************************************)
EXTENDS EWD840_proofModel

(***************************************************************************)
(* The algorithm is type-correct: TypeOK is an inductive invariant.        *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Prove the main soundness property of the algorithm by (1) proving that  *)
(* Inv is an inductive invariant and (2) that it implies correctness.      *)
(***************************************************************************)
=============================================================================
