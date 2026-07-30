---------------------------- MODULE EWD998PCal_proof_InitiatorIsZeroScaffold ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998PCal specification.             *)
(*                                                                         *)
(* The EWD998PCal module is a PlusCal-translated version of EWD998 in      *)
(* which the per-node `pending` counter and the global `token` of EWD998   *)
(* are replaced by a single `network` variable holding a per-node bag of   *)
(* messages (payload "pl" messages and the unique token "tok" message).   *)
(* The refinement mapping (in EWD998PCal.tla) recovers EWD998's `pending` *)
(* and `token` from `network`:                                            *)
(*                                                                         *)
(*   pending = [n |-> count of [type|->"pl"] in network[n]]                *)
(*   token   = the unique tok msg in the network, with its position       *)
(*                                                                         *)
(* This module proves the safety part of the refinement,                   *)
(*                                                                         *)
(*   THEOREM Refinement == Spec => EWD998Spec                              *)
(*                                                                         *)
(* where EWD998Spec == EWD998!Init /\ [][EWD998!Next]_EWD998!vars (no     *)
(* fairness; the comment in the spec explains why).                       *)
(*                                                                         *)
(* The proof shape mirrors EWD998_proof.tla's `Refinement` theorem:       *)
(* an inductive invariant (network well-formedness + Safra's invariant   *)
(* transferred to PCal) plus a per-disjunct case analysis.                *)
(***************************************************************************)
EXTENDS EWD998PCal, TLAPS

\* The spec defines `Initiator == 0`; expose it as a fact for TLAPS.
=============================================================================
