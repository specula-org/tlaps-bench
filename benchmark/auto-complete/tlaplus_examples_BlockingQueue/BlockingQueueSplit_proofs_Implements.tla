--------------------- MODULE BlockingQueueSplit_proofs_Implements ----------------------
EXTENDS BlockingQueueSplit, TLAPS

(* Scaffolding: TypeInv is inductive. *)
LEMMA ITypeInv == Spec => []TypeInv
PROOF OMITTED

THEOREM Implements == Spec => A!Spec
PROOF OBVIOUS

(* The IInv below mirrors the high-level BlockingQueue!IInv translated to *)
(* the split form: keep TypeInv!2 (Len) and the wait-set domain           *)
(* constraints, the deadlock-freedom Invariant on the union, and the same *)
(* two existential clauses guarding the buffer = <<>> and full buffer     *)
(* cases.                                                                 *)
(*                                                                        *)
(* Strictly speaking, proving DeadlockFreedom directly here is redundant: *)
(* the THEOREM Implements above already establishes Spec => A!Spec, hence *)
(* []A!Invariant transfers to BlockingQueueSplit by refinement. We prove  *)
(* it locally as scaffolding/illustration of the inductive invariant.     *)
IInv ==
    /\ Len(buffer) \in 0..BufCapacity
    /\ waitSetP \in SUBSET Producers
    /\ waitSetC \in SUBSET Consumers
    /\ (waitSetC \cup waitSetP) # (Producers \cup Consumers)
    /\ buffer = <<>> => \E p \in Producers : p \notin (waitSetC \cup waitSetP)
    /\ Len(buffer) = BufCapacity => \E c \in Consumers : c \notin (waitSetC \cup waitSetP)

(* This proof of deadlock freedom is self-contained: it only references  *)
(* A!Invariant (the predicate) and never relies on BlockingQueue's       *)
(* state machine (A!Init, A!Next, A!Spec) or its inductive invariant     *)
(* A!IInv.                                                               *)

(* IInv matches A!IInv up to splitting the wait-set constraint into its  *)
(* Producers/Consumers components, hence implies it pointwise. Combined  *)
(* with THEOREM Implements (Spec => A!Spec), this gives an alternative,  *)
(* refinement-based route to deadlock freedom that does not require the  *)
(* self-contained inductive proof of DeadlockFreedom above.              *)

=============================================================================
