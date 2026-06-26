--------------------------- MODULE Simple_proof_InvInvariant -------------------------------
(***************************************************************************)
(* Wrapper theorems exposing TypeOK and Inv as named invariants of Spec.  *)
(* The actual inductive content is already in Simple.tla's `Correctness`. *)
(***************************************************************************)
EXTENDS Simple

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM InvInvariant == Spec => []Inv
PROOF OBVIOUS
============================================================================
