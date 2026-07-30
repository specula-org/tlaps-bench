------------------- MODULE SyncTerminationDetection_proof_QuiescentScaffold -------------------
(***************************************************************************)
(* Proofs of the properties asserted in module SyncTerminationDetection.   *)
(***************************************************************************)
EXTENDS SyncTerminationDetection, TLAPS

(* Proofs of safety properties *)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM CorrectDetection == Spec => TDCorrect
PROOF OMITTED

=============================================================================
