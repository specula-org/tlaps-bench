---------------------------- MODULE EWD840_proof_Round1 ----------------------------
(***************************************************************************)
(* This module contains the proof of the safety properties of Dijkstra's   *)
(* termination detection algorithm. Checking the proof requires TLAPS to   *)
(* be installed.                                                           *)
(***************************************************************************)
EXTENDS EWD840_proof
USE NAssumption

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
LEMMA EnabledSystem ==
    ASSUME TypeOK 
    PROVE  (ENABLED <<System>>_vars) <=> 
              \/ tpos = 0 /\ (tcolor = "black" \/ color[0] = "black")
              \/ tpos \in Node \ {0} /\ (~active[tpos] \/ tcolor = "black" \/ color[tpos] = "black")
PROOF OMITTED

(***************************************************************************)
(* We need to prove that once the system has globally terminated, the      *)
(* condition for detecting termination must eventually become true. As is  *)
(* often the case with proving liveness, it is convenient to carry out     *)
(* this proof by contradiction, so we also assume that termination is      *)
(* never detected. The system may require three rounds:                    *)
(* 1. The first round brings the token back to node 0.                     *)
(* 2. The second round cleans all nodes.                                   *)
(* 3. The third round brings back a clean token.                           *)
(***************************************************************************)

(***************************************************************************)
(* Specification used for the liveness proof: we ignore the initial state  *)
(* predicate but include the invariants of the algorithm. We also assume,  *)
(* for the sake of contradiction, that termination is never detected.      *)
(***************************************************************************)

allWhite == \A n \in Node : color[n] = "white"

(***************************************************************************)
(* The following three lemmas represent the idea of the system needing up  *)
(* to three complete rounds of the token for detecting termination. Their  *)
(* proofs rely on induction on the initial position of the token, and they *)
(* are essentially obtained by copy-and-paste.                             *)
(***************************************************************************)
LEMMA Round1 ==
    TSpec => (terminated ~> (terminated /\ tpos = 0))
PROOF OBVIOUS

(***************************************************************************)
(* Liveness is a simple consequence of the above lemmas.                   *)
(***************************************************************************)

(***************************************************************************)
(* The algorithm implements the high-level specification of termination    *)
(* detection in a ring with synchronous communication between nodes.       *)
(* Note that the parameters of the module SyncTerminationDetection are     *)
(* instantiated by the symbols of the same name in the present module.     *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
