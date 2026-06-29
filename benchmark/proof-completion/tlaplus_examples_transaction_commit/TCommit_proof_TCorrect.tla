--------------------------- MODULE TCommit_proof_TCorrect ---------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)                        *)
(* stated in TCommit.tla.                                                  *)
(***************************************************************************)
EXTENDS TCommit, TLAPS

Inv == TCTypeOK /\ TCConsistent

THEOREM TCorrect == TCSpec => []Inv
PROOF OBVIOUS

============================================================================
