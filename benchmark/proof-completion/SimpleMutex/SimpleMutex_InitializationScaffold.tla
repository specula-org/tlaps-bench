----------------------------- MODULE SimpleMutex_InitializationScaffold -----------------------------
EXTENDS SimpleMutexModel

(***********

(***************************************************************************)
(* The following algorithm is an important mutual exclusion protocol.      *)
(* This protocol is at the heart of many mutual exclusion algorithms.  It  *)
(* is a two-process protocol that guarantees that both processes cannot    *)
(* execute statement cs.  (However, they can both deadlock.)               *)
(***************************************************************************)
--algorithm Mutex {
  variable trying = [i \in {0,1} |-> FALSE]

  process (p \in {0,1}) {
a:   trying[self] := TRUE ;
b:   await ~trying[1 - self];
cs:  skip  \* the critical section
   }
}

***********)

\* BEGIN TRANSLATION

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK ==
  /\ trying \in [{0,1} -> BOOLEAN]
  /\ pc \in [{0,1} -> {"a", "b", "cs", "Done"}]

Inv == \A i \in {0,1} :
          /\ pc[i] \in {"b", "cs"} => trying[i]
          /\ pc[i] = "cs" => pc[1-i] # "cs"

IndInvSpec == (TypeOK /\ Inv) /\ [][Next]_vars
   (************************************************************************)
   (* TypeOK /\ Inv is an inductive invariant Spec iff it is an invariant  *)
   (* of IndInvSpec.  TLC can be used to check what we are about to prove. *)
   (************************************************************************)

(***************************************************************************)
(* The following theorem asserts that TypeOK /\ Inv is true in the initial *)
(* state.                                                                  *)
(***************************************************************************)
=============================================================================
