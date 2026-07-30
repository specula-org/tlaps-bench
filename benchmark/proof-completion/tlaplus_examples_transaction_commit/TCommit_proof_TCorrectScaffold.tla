--------------------------- MODULE TCommit_proof_TCorrectScaffold ---------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)                        *)
(* stated in TCommit.tla.                                                  *)
(***************************************************************************)
EXTENDS TCommit, TLAPS

Inv == TCTypeOK /\ TCConsistent

=============================================================================
