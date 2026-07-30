---------------------- MODULE AsyncTerminationDetection_proof_SafetyScaffold ---------------------
(*********************************************************************************)
(* Proofs about the high-level specification of termination detection.           *)
(*********************************************************************************)

EXTENDS AsyncTerminationDetection, TLAPS

LEMMA TypeCorrect == Init /\ [][Next]_vars => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)
=============================================================================
