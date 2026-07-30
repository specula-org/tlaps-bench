--------------------------- MODULE EWD687a_proof_TypeCorrectScaffold ---------------------------
(***************************************************************************)
(* Proofs of the theorems stated in EWD687a.tla.                           *)
(***************************************************************************)
EXTENDS EWD687a, NaturalsInduction, FiniteSetTheorems, GraphTheorems, TLAPS

(***************************************************************************)
(* Theorem 1: Spec => CountersConsistent                                   *)
(*                                                                         *)
(* The four counters per edge are always consistent: the number of         *)
(* messages ever sent on an edge equals the messages received and          *)
(* acknowledged plus the messages received and not yet acked plus the      *)
(* acks in flight plus the messages still in flight.                       *)
(*                                                                         *)
(* TypeOK on its own is not inductive: in RcvAck and SendAck a counter is  *)
(* decremented, and we can only show that the result stays in Nat by also  *)
(* knowing the counters are consistent.  We therefore prove TypeOK and the *)
(* state predicate Counters together as a single inductive invariant.     *)
(***************************************************************************)
Inv1 == TypeOK /\ CountersConsistent

THEOREM Invariant1 == Spec => []Inv1 
PROOF OMITTED

=============================================================================
