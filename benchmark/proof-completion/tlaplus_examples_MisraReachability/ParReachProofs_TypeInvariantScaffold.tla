--------------------------- MODULE ParReachProofs_TypeInvariantScaffold ---------------------------
(***************************************************************************)
(* This module contains TLAPS checked proofs of the safety properties      *)
(* asserted in module ParReach--namely, the invariance of Inv and that the *)
(* parallel algorithm implements the safety part of Misra's algorithm under *)
(* the refinement mapping defined there.                                   *)
(***************************************************************************)
EXTENDS ParReach, Integers, TLAPS

=============================================================================
