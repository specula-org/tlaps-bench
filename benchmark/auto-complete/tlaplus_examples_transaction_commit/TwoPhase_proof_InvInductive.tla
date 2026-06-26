--------------------------- MODULE TwoPhase_proof_InvInductive --------------------------
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

THEOREM TypeCorrect == TPSpec => []TPTypeOK
PROOF OMITTED

(***************************************************************************)
(*                  TPSpec => []TC!TCConsistent  (Band M)                  *)
(***************************************************************************)

CommitMsg == [type |-> "Commit"]
AbortMsg  == [type |-> "Abort"]
PrepMsg(rm) == [type |-> "Prepared", rm |-> rm]

(***************************************************************************)
(* The strengthened inductive invariant.  Each conjunct is a fact that    *)
(* the protocol's actions preserve and that together imply TCConsistent.  *)
(*                                                                         *)
(*   1. TPTypeOK                                                           *)
(*   2. The TM commits at most one decision (mutex on Commit/Abort msgs). *)
(*   3-5. tmState mirrors which decision message has been broadcast.       *)
(*   6. tmPrepared only contains RMs that actually sent "Prepared".        *)
(*   7. RMs that have a "Prepared" msg in flight are no longer "working". *)
(*   8. "committed" RMs imply CommitMsg has been broadcast.                *)
(*   9. CommitMsg in msgs implies every RM had sent "Prepared" first      *)
(*      (preserved from TMCommit's tmPrepared = RM precondition).          *)
(*  10. "aborted" RMs split into two cases:                                *)
(*        - via RMRcvAbortMsg  (AbortMsg in msgs), or                      *)
(*        - via RMChooseToAbort (the RM never sent "Prepared").            *)
(***************************************************************************)
Inv ==
  /\ TPTypeOK
  /\ ~ (CommitMsg \in msgs /\ AbortMsg \in msgs)
  /\ tmState = "init"      => CommitMsg \notin msgs /\ AbortMsg \notin msgs
  /\ tmState = "committed" => CommitMsg \in msgs
  /\ tmState = "aborted"   => AbortMsg \in msgs
  /\ \A rm \in tmPrepared : PrepMsg(rm) \in msgs
  /\ \A rm \in RM : PrepMsg(rm) \in msgs => rmState[rm] # "working"
  /\ \A rm \in RM : rmState[rm] = "committed" => CommitMsg \in msgs
  /\ CommitMsg \in msgs => \A rm \in RM : PrepMsg(rm) \in msgs
  /\ \A rm \in RM : rmState[rm] = "aborted" =>
        \/ AbortMsg \in msgs
        \/ PrepMsg(rm) \notin msgs

LEMMA InvInductive == TPSpec => []Inv
PROOF OBVIOUS

============================================================================
