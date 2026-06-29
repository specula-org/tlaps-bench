---------------------------- MODULE FindHighest_IsCorrect -----------------------------
(***************************************************************************)
(* Defines a very simple algorithm that finds the largest value in a       *)
(* sequence of Natural numbers. This was created as an exercise in finding *)
(* & proving type invariants, inductive invariants, and correctness.       *)
(***************************************************************************)

EXTENDS FindHighest

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
THEOREM TypeInvariantHolds == Spec => []TypeOK
\* To prove theorems like Spec => []Invariant, you have to:
\*  1. Prove Invariant holds in the initial state (usually trivial)
\*  2. Prove Invariant holds when variables are unchanged (usually trivial)
\*  3. Prove that assuming Invariant is true, a Next step implies Invariant'
\* The last one (inductive case) is usually quite difficult. It helps to
\* never forget you have an extremely powerful assumption: that Invariant is
\* true!
PROOF OMITTED

\* The inductive invariant; writing these is an art. You want an invariant
\* that can be shown to be true in every state, and if it's true in all
\* states, it can be shown to imply algorithm correctness as a whole.
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF OMITTED

\* A small sub-theorem that relates our inductive invariant to correctness
DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF OMITTED

\* The main event! After the algorithm has terminated, the variable h must
\* have value greater than or equal to any element of the sequence.
Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

\* Correctness is implied by the preceding invariants.
THEOREM IsCorrect == Spec => []Correctness
PROOF OBVIOUS

=============================================================================

