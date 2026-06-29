---------------------- MODULE AsyncTerminationDetection_proof_Liveness ---------------------
(*********************************************************************************)
(* Proofs about the high-level specification of termination detection.           *)
(*********************************************************************************)

EXTENDS AsyncTerminationDetection, TLAPS

LEMMA TypeCorrect == Init /\ [][Next]_vars => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)
THEOREM Safety == Init /\ [][Next]_vars => []Safe
PROOF OMITTED

THEOREM Stability == Init /\ [][Next]_vars => Quiescence
PROOF OMITTED

(***************************************************************************)
(* Proofs of liveness.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first reduce the enabledness condition that appears in the fairness  *)
(* hypothesis to a standard state predicate.                               *)
(***************************************************************************)
LEMMA EnabledDT == 
  ASSUME TypeOK 
  PROVE  (ENABLED <<DetectTermination>>_vars) <=> (terminated /\ ~ terminationDetected)
PROOF OMITTED

THEOREM Liveness == Spec => Live
PROOF OBVIOUS

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by merz
