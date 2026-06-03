------------------------- MODULE ivy_examples_ticket -------------------------
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* TLA+ translation of Ivy's examples/liveness/ticket.ivy.                 *)
(*                                                                         *)
(* The Ivy model leaves the thread type uninterpreted and axiomatizes an   *)
(* ordered ticket type with zero and successor.  This TLA+ model keeps     *)
(* Thread as a constant set and represents tickets with Nat, zero with 0,  *)
(* le with <=, and succ(x) with x + 1.                                     *)
(*                                                                         *)
(* Intentional TLA+ refactoring: Ivy uses a transient ghost relation        *)
(* scheduled(T) and a no-op step22 action to state scheduler fairness as   *)
(* "every thread is scheduled infinitely often".  This module follows the  *)
(* usual TLA+ convention instead: the no-op wait step is represented by    *)
(* stuttering in [][Next]_vars, and fairness is stated directly as weak    *)
(* fairness of each thread's real progress action Step(t).                 *)
(***************************************************************************)

CONSTANT Thread

ASSUME ThreadAssumption == Thread # {}

VARIABLES pc, service, next_ticket, m

vars == << pc, service, next_ticket, m >>

PC == {"Idle", "Waiting", "Critical"}

Init ==
  /\ pc = [t \in Thread |-> "Idle"]
  /\ service = 0
  /\ next_ticket = 0
  /\ m = [t \in Thread |-> 0]

TakeTicket(t) ==
  /\ t \in Thread
  /\ pc[t] = "Idle"
  /\ pc' = [pc EXCEPT ![t] = "Waiting"]
  /\ service' = service
  /\ next_ticket' = next_ticket + 1
  /\ m' = [m EXCEPT ![t] = next_ticket]

EnterCritical(t, k) ==
  /\ t \in Thread
  /\ k \in Nat
  /\ pc[t] = "Waiting"
  /\ m[t] = k
  /\ k <= service
  /\ pc' = [pc EXCEPT ![t] = "Critical"]
  /\ UNCHANGED << service, next_ticket, m >>

LeaveCritical(t) ==
  /\ t \in Thread
  /\ pc[t] = "Critical"
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ service' = service + 1
  /\ next_ticket' = next_ticket
  /\ m' = m

Step(t) ==
  \/ TakeTicket(t)
  \/ \E k \in Nat : EnterCritical(t, k)
  \/ LeaveCritical(t)

Next ==
  \E t \in Thread : Step(t)

SafetySpec ==
  /\ Init
  /\ [][Next]_vars

Spec ==
  /\ SafetySpec
  /\ \A t \in Thread : WF_vars(Step(t))

MutualExclusion ==
  \A t1, t2 \in Thread :
    (pc[t1] = "Critical" /\ pc[t2] = "Critical") => t1 = t2

THEOREM Safety == SafetySpec => []MutualExclusion
  PROOF OMITTED

(***************************************************************************)
(* Temporal property corresponding to Ivy's nonstarvation property.        *)
(*                                                                         *)
(* Ivy writes the assumption using scheduled(T).  Here that assumption is  *)
(* replaced by the weak-fairness conjuncts in Spec, so the liveness        *)
(* property is just the conclusion:                                        *)
(*   forall T. globally ~(Waiting(T) & globally ~Critical(T)).             *)
(* The conclusion is equivalently: every waiting thread eventually reaches *)
(* the critical section.                                                   *)
(***************************************************************************)

NonStarvation ==
  \A t \in Thread : (pc[t] = "Waiting") ~> (pc[t] = "Critical")

THEOREM Liveness == Spec => NonStarvation
  PROOF OMITTED

=============================================================================
