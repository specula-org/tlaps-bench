------------------- MODULE SyncTerminationDetection_proof_Enabled_STScaffold -------------------
(***************************************************************************)
(* Proofs of the properties asserted in module SyncTerminationDetection.   *)
(***************************************************************************)
EXTENDS SyncTerminationDetection, TLAPS

(* Proofs of safety properties *)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM CorrectDetection == Spec => TDCorrect
PROOF OMITTED

THEOREM Quiescent == Spec => Quiescence
PROOF OMITTED

(* Proof of liveness *)

(****************************************************************************)
(* The following lemma reduces the enabledness condition underlying the     *)
(* fairness condition to a simple state predicate.                          *)
(****************************************************************************)
=============================================================================
