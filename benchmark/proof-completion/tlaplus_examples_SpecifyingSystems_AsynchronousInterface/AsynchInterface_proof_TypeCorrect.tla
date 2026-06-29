------------------------ MODULE AsynchInterface_proof_TypeCorrect ----------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in AsynchInterface.tla.               *)
(***************************************************************************)
EXTENDS AsynchInterface, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
