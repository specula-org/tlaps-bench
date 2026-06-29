---------------------- MODULE AsyncTerminationDetection_proof_TypeCorrect ---------------------
(*********************************************************************************)
(* Proofs about the high-level specification of termination detection.           *)
(*********************************************************************************)

EXTENDS AsyncTerminationDetection, TLAPS

LEMMA TypeCorrect == Init /\ [][Next]_vars => []TypeOK
PROOF OBVIOUS

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)

(***************************************************************************)
(* Proofs of liveness.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first reduce the enabledness condition that appears in the fairness  *)
(* hypothesis to a standard state predicate.                               *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by merz
