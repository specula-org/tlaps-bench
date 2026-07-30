---------------------------- MODULE EWD840_proof_TypeCorrectScaffold ----------------------------
(***************************************************************************)
(* This module contains the proof of the safety properties of Dijkstra's   *)
(* termination detection algorithm. Checking the proof requires TLAPS to   *)
(* be installed.                                                           *)
(***************************************************************************)
EXTENDS EWD840_proofModel

(***************************************************************************)
(* The algorithm is type-correct: TypeOK is an inductive invariant.        *)
(***************************************************************************)
=============================================================================
