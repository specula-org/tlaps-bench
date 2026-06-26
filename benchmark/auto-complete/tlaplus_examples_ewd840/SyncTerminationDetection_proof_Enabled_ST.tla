------------------- MODULE SyncTerminationDetection_proof_Enabled_ST -------------------
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
LEMMA Enabled_ST == 
    ASSUME TypeOK
    PROVE (ENABLED <<DetectTermination>>_vars) <=> terminated /\ ~terminationDetected
PROOF OBVIOUS

(****************************************************************************)
(* Proving liveness is easy since a single occurrence of the helpful action *)
(* DetectTermination leads to the desired state.                            *)
(****************************************************************************)

=============================================================================
