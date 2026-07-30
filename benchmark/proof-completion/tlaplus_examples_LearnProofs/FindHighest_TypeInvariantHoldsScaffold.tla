---------------------------- MODULE FindHighest_TypeInvariantHoldsScaffold -----------------------------
(***************************************************************************)
(* Defines a very simple algorithm that finds the largest value in a       *)
(* sequence of Natural numbers. This was created as an exercise in finding *)
(* & proving type invariants, inductive invariants, and correctness.       *)
(***************************************************************************)

EXTENDS FindHighestModel

(****************************************************************************
--algorithm Highest {
  variables
    f \in Seq(Nat);
    h = -1;
    i = 1;
  define {
    max(a, b) == IF a >= b THEN a ELSE b
  } {
lb: while (i <= Len(f)) {
      h := max(h, f[i]);
      i := i + 1;
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "31f24270" /\ chksum(tla) = "819802c6")

(* define statement *)

(* Allow infinite stuttering to prevent deadlock on termination. *)

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* The type invariant; the proof system likes knowing variables are in Nat.
\* It's a good idea to check these invariants with the model checker before
\* trying to prove them. To quote Leslie Lamport, it's very difficult to
\* prove something that isn't true!
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}

\* It's useful to prove the type invariant first, so it can be used as an
\* assumption in further proofs to restrict variable values.
=============================================================================
