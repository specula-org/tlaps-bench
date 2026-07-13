-------------------------- MODULE two_thread_mutex -------------------------
EXTENDS TLAPS

(***************************************************************************)
(* TLA+ model corresponding to anvil-verifier/anvil's src/tla_demo.rs.     *)
(*                                                                         *)
(* The Rust model has two thread identifiers, A and B.  Each thread starts *)
(* in Waiting, can acquire the lock and move to Holding, then can release  *)
(* the lock and move to Terminated.  The temporal model assumes weak       *)
(* fairness for each acquire and release action.                           *)
(***************************************************************************)

VARIABLES lock, threads

vars == << lock, threads >>

Tid == {"A", "B"}

ThreadState == {"Waiting", "Holding", "Terminated"}

TypeOK ==
  /\ lock \in BOOLEAN
  /\ threads \in [Tid -> ThreadState]

Init ==
  /\ lock = FALSE
  /\ threads = [tid \in Tid |-> "Waiting"]

Acquire(tid) ==
  /\ tid \in Tid
  /\ lock = FALSE
  /\ threads[tid] = "Waiting"
  /\ lock' = TRUE
  /\ threads' = [threads EXCEPT ![tid] = "Holding"]

Release(tid) ==
  /\ tid \in Tid
  /\ threads[tid] = "Holding"
  /\ lock' = FALSE
  /\ threads' = [threads EXCEPT ![tid] = "Terminated"]

Next ==
  \/ \E tid \in Tid : Acquire(tid)
  \/ \E tid \in Tid : Release(tid)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A tid \in Tid :
       /\ WF_vars(Acquire(tid))
       /\ WF_vars(Release(tid))

BothThreadsTerminated ==
  \A tid \in Tid : threads[tid] = "Terminated"

Termination ==
  <>BothThreadsTerminated

MutualExclusion ==
  ~(threads["A"] = "Holding" /\ threads["B"] = "Holding")

THEOREM Liveness == Spec => Termination
  PROOF OMITTED

=============================================================================
