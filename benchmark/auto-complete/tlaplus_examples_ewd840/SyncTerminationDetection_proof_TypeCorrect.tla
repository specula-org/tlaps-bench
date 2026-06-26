------------------- MODULE SyncTerminationDetection_proof_TypeCorrect -------------------
(***************************************************************************)
(* Proofs of the properties asserted in module SyncTerminationDetection.   *)
(***************************************************************************)
EXTENDS SyncTerminationDetection, TLAPS

(* Proofs of safety properties *)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

(* Proof of liveness *)

(****************************************************************************)
(* The following lemma reduces the enabledness condition underlying the     *)
(* fairness condition to a simple state predicate.                          *)
(****************************************************************************)

(****************************************************************************)
(* Proving liveness is easy since a single occurrence of the helpful action *)
(* DetectTermination leads to the desired state.                            *)
(****************************************************************************)

=============================================================================
