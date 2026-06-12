-------------------------- MODULE ivy_examples_split_queue_2_new --------------------------
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* TLA+ translation of Ivy's examples/liveness/split_queue_2_new.ivy.      *)
(*                                                                         *)
(* The Ivy model is parameterized by an unbounded ordered sequence type     *)
(* lclock.  This TLA+ model uses Nat for that order: 0 is the first cell   *)
(* and <, <= are the usual natural-number orders.                           *)
(*                                                                         *)
(* The queue is split by Boolean kind.  A send creates a work item at a    *)
(* fresh index greater than every existing begun index.  The send action   *)
(* may leave gaps in the index space.  Receiver 1 can complete the least   *)
(* unfinished item only when its kind is TRUE; receiver 2 can complete the *)
(* least unfinished item only when its kind is FALSE.                       *)
(*                                                                         *)
(* Ivy's trying1.now and trying2.now are transient signal events raised by *)
(* recv1 and recv2.  They are not persistent protocol state.  Following    *)
(* the convention used by the other Ivy translations in this repository,   *)
(* this module omits those transient flags and states their useful effect  *)
(* as weak fairness of the two real progress actions Recv1 and Recv2.      *)
(* No-op receive attempts are represented by ordinary stuttering steps.    *)
(*                                                                         *)
(* Ivy's implementation section introduces firstq as a prophecy/proof      *)
(* variable for the next queue cell to complete.  Here firstq is retained  *)
(* as a ghost variable and maintained as the least begun but not done cell *)
(* whenever such a cell exists.                                             *)
(***************************************************************************)

VARIABLES begun, done, queue, firstq

vars == << begun, done, queue, firstq >>

HasUndoneFrom(b, d) ==
  \E x \in Nat : b[x] /\ ~d[x]

FirstUndoneFrom(x, b, d) ==
  /\ x \in Nat
  /\ b[x]
  /\ ~d[x]
  /\ \A y \in Nat : (b[y] /\ ~d[y]) => x <= y

UpdateFirstq(b, d) ==
  IF HasUndoneFrom(b, d)
    THEN FirstUndoneFrom(firstq', b, d)
    ELSE firstq' = firstq

Init ==
  /\ begun = [x \in Nat |-> FALSE]
  /\ done = [x \in Nat |-> FALSE]
  /\ queue \in [Nat -> BOOLEAN]
  /\ firstq = 0

(***************************************************************************)
(* Send(lt, kind) begins a new work item.  The new index lt must be larger *)
(* than every index that has already begun, which also implies lt itself   *)
(* was not already begun.                                                   *)
(***************************************************************************)

Send(lt, kind) ==
  /\ lt \in Nat
  /\ kind \in BOOLEAN
  /\ \A x \in Nat : begun[x] => x < lt
  /\ begun' = [begun EXCEPT ![lt] = TRUE]
  /\ queue' = [queue EXCEPT ![lt] = kind]
  /\ UpdateFirstq(begun', done)
  /\ UNCHANGED done

(***************************************************************************)
(* Recv1 completes the least unfinished item when that item has kind TRUE. *)
(* If the least unfinished item has the other kind, Ivy's recv1 only raises *)
(* its transient trying signal and makes no persistent state change; that  *)
(* no-op case is represented by stuttering here.                            *)
(***************************************************************************)

Recv1 ==
  \E x \in Nat :
    /\ FirstUndoneFrom(x, begun, done)
    /\ queue[x]
    /\ done' = [done EXCEPT ![x] = TRUE]
    /\ UpdateFirstq(begun, done')
    /\ UNCHANGED << begun, queue >>

(***************************************************************************)
(* Recv2 is the symmetric receiver for kind FALSE.                          *)
(***************************************************************************)

Recv2 ==
  \E x \in Nat :
    /\ FirstUndoneFrom(x, begun, done)
    /\ ~queue[x]
    /\ done' = [done EXCEPT ![x] = TRUE]
    /\ UpdateFirstq(begun, done')
    /\ UNCHANGED << begun, queue >>

Next ==
  \/ \E lt \in Nat, kind \in BOOLEAN : Send(lt, kind)
  \/ Recv1
  \/ Recv2

SafetySpec ==
  /\ Init
  /\ [][Next]_vars

Spec ==
  /\ SafetySpec
  /\ WF_vars(Recv1)
  /\ WF_vars(Recv2)

(***************************************************************************)
(* Temporal property corresponding to Ivy's lemma1.                        *)
(*                                                                         *)
(* Ivy states: if both receive attempts happen infinitely often, then any  *)
(* work cell that is globally begun is eventually done.  Since begun is    *)
(* monotonic in this model, the same useful response property is expressed *)
(* directly as a leads-to formula: once a cell has begun, it is eventually *)
(* marked done.                                                            *)
(***************************************************************************)

WorkCompletion ==
  \A x \in Nat : begun[x] ~> done[x]

THEOREM Liveness == Spec => WorkCompletion
  PROOF OMITTED

===========================================================================================
