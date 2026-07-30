--------------------------- MODULE TwoPhase_proof_TypeCorrectScaffold --------------------------
(***************************************************************************)
(* TLAPS proofs of TwoPhase.tla theorems:                                  *)
(*                                                                         *)
(*   TPSpec => []TPTypeOK            (Band E, directly inductive)          *)
(*   TPSpec => []TC!TCConsistent     (Band M, no conflicting decisions)    *)
(*                                                                         *)
(* TC!TCConsistent says no two RMs end up "committed" and "aborted"        *)
(* simultaneously.  It is not directly inductive; the strengthening below *)
(* tracks the message-sequencing facts that explain why the TM-broadcast  *)
(* "Commit" and "Abort" decisions are mutually exclusive, and how each    *)
(* RM's local state correlates with what is on the wire.                   *)
(*                                                                         *)
(* The candidate inductive invariant was first validated with Apalache    *)
(* (per Konnov/Kuppe/Merz, arXiv:2211.07216 Sec. 3.2) on a finite         *)
(* instance with 3 RMs:                                                    *)
(*                                                                         *)
(*   TPInit  /\ [TPNext]_vars |=0  Inv      (initial states satisfy Inv) *)
(*   InvInit /\ [TPNext]_vars |=1  Inv      (Inv is preserved one step)  *)
(*   Inv => TCConsistent                    (Inv implies the goal)        *)
(***************************************************************************)
EXTENDS TwoPhase, TLAPS

(***************************************************************************)
(*                            TPSpec => []TPTypeOK                         *)
(***************************************************************************)

=============================================================================
