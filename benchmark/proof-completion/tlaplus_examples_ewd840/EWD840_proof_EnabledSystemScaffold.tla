---------------------------- MODULE EWD840_proof_EnabledSystemScaffold ----------------------------
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
THEOREM Invariant == Spec => []Inv
PROOF OMITTED

THEOREM Safety == Spec => []TerminationDetection
PROOF OMITTED

(***************************************************************************)
(* The above proof shows that Dijkstra's invariant implies the predicate   *)
(* TerminationDetection. If you find that one-line proof too obscure, here *)
(* is a more detailed, hierarchical proof of that same implication.        *)
(***************************************************************************)
LEMMA Inv => TerminationDetection
PROOF OMITTED

(***************************************************************************)
(* Liveness of the algorithm.                                              *)
(***************************************************************************)

(***************************************************************************)
(* The proof of liveness relies on the fairness condition assumed for the  *)
(* algorithm, which in turn is defined in terms of enabledness. It is      *)
(* usually a good idea to reduce that enabledness condition to a standard  *)
(* state predicate, and the following lemma does just that.                *)
(***************************************************************************)
=============================================================================
