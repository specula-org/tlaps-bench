--------------------------- MODULE Channel_proof_TypeCorrect ---------------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in Channel.tla.                       *)
(***************************************************************************)
EXTENDS Channel, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
