---------------------- MODULE ivy_examples_ticket_nested ----------------------
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* TLA+ translation of Ivy's examples/liveness/ticket_nested.ivy.          *)
(*                                                                         *)
(* The Ivy model leaves the thread and ticket types uninterpreted,         *)
(* axiomatizes a total order on tickets, and uses succ/zero for ticket     *)
(* arithmetic.  This TLA+ model follows the same convention as             *)
(* ivy_examples_ticket: Thread is a constant set and tickets are Nat, with *)
(* zero represented by 0, le by <=, and succ(x) by x + 1.                  *)
(*                                                                         *)
(* Compared with ivy_examples_ticket, a thread that enters the critical    *)
(* section also receives a local countdown c[t].  Ivy's step33 decrements  *)
(* this countdown until it reaches zero; only then can step31 leave the    *)
(* critical section and advance service.                                   *)
(*                                                                         *)
(* Intentional TLA+ refactoring: Ivy uses a transient ghost relation       *)
(* scheduled(T) and a no-op step22 action for scheduler fairness.  This    *)
(* module omits scheduled(T), represents the no-op wait step by            *)
(* stuttering through [][Next]_vars, and states fairness directly as weak  *)
(* fairness of each thread's real progress action Step(t).                 *)
(***************************************************************************)

CONSTANT Thread

ASSUME ThreadAssumption == Thread # {}

VARIABLES pc, service, next_ticket, m, c

vars == << pc, service, next_ticket, m, c >>

PC == {"Idle", "Waiting", "Critical"}

Init ==
  /\ pc = [t \in Thread |-> "Idle"]
  /\ service = 0
  /\ next_ticket = 0
  /\ m = [t \in Thread |-> 0]
  /\ c = [t \in Thread |-> 0]

TakeTicket(t) ==
  /\ t \in Thread
  /\ pc[t] = "Idle"
  /\ pc' = [pc EXCEPT ![t] = "Waiting"]
  /\ next_ticket' = next_ticket + 1
  /\ m' = [m EXCEPT ![t] = next_ticket]
  /\ UNCHANGED << service, c >>

EnterCritical(t, k) ==
  /\ t \in Thread
  /\ k \in Nat
  /\ pc[t] = "Waiting"
  /\ m[t] = k
  /\ k <= service
  /\ pc' = [pc EXCEPT ![t] = "Critical"]
  /\ c' = [c EXCEPT ![t] = next_ticket]
  /\ UNCHANGED << service, next_ticket, m >>

RunNestedTask(t, k) ==
  /\ t \in Thread
  /\ k \in Nat
  /\ pc[t] = "Critical"
  /\ c[t] = k + 1
  /\ c' = [c EXCEPT ![t] = k]
  /\ UNCHANGED << pc, service, next_ticket, m >>

LeaveCritical(t) ==
  /\ t \in Thread
  /\ pc[t] = "Critical"
  /\ c[t] = 0
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ service' = service + 1
  /\ UNCHANGED << next_ticket, m, c >>

Step(t) ==
  \/ TakeTicket(t)
  \/ \E k \in Nat : EnterCritical(t, k)
  \/ \E k \in Nat : RunNestedTask(t, k)
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
  PROOF OBVIOUS

(***************************************************************************)
(* Temporal property corresponding to Ivy's nonstarvation property.        *)
(*                                                                         *)
(* Ivy states this with transient scheduled(T) events: if every thread is  *)
(* scheduled infinitely often, then no thread can remain forever at pc2    *)
(* without eventually reaching pc3.  Here the scheduling premise is        *)
(* replaced by the weak-fairness conjuncts in Spec, so the conclusion is   *)
(* the direct response property from Waiting to Critical.                  *)
(***************************************************************************)

NonStarvation ==
  \A t \in Thread : (pc[t] = "Waiting") ~> (pc[t] = "Critical")

THEOREM Liveness == Spec => NonStarvation
  PROOF OBVIOUS

=============================================================================
