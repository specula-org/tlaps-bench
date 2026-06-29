--------------------------- MODULE SimpleRegular_proof_InvInvariant ------------------------
(***************************************************************************)
(* Wrapper theorems exposing TypeOK and Inv as named invariants of Spec.  *)
(* The inductive content is already in SimpleRegular.tla's Correctness.   *)
(***************************************************************************)
EXTENDS SimpleRegular, TLAPS

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM InvInvariant == Spec => []Inv
PROOF OBVIOUS
============================================================================
