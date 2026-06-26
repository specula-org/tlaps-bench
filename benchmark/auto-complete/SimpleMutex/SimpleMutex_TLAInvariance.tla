----------------------------- MODULE SimpleMutex_TLAInvariance -----------------------------
EXTENDS SimpleMutex

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
THEOREM Initialization == Init => TypeOK /\ Inv
PROOF OMITTED

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

(***************************************************************************)
(* The following theorem asserts that our invariant implies mutual         *)
(* exclusion.                                                              *)
(***************************************************************************)
THEOREM Mutex == Inv => MutualExclusion
PROOF OMITTED

(***************************************************************************)
(* The following theorem asserts that if a step (a pair of states)         *)
(* satisfies the formula Next, and TypeOK /\ Inv is true in the first      *)
(* state, then TypeOK /\ Inv is true in the second state.                  *)
(*                                                                         *)
(* This proof was written before the implementation of TLAPS's SMT backend *)
(* prover. For the much simpler proof using that backend, see below.       *) 
(***************************************************************************)
THEOREM Invariance == TypeOK /\ Inv /\ Next => TypeOK' /\ Inv'
PROOF OMITTED

(****************************************************************************)
(* The same theorem proved with the help of the SMT backend.                *)
(****************************************************************************)
THEOREM
  ASSUME TypeOK, Inv, Next
  PROVE  TypeOK' /\ Inv'
PROOF OMITTED
(***************************************************************************)
(* The following is a trivial consequence of the Invariance theorem, the   *)
(* definition of [Next]_vars, and the fact that UNCHANGED vars implies     *)
(* that none of the declared variables changes.                            *)
(***************************************************************************)
THEOREM TLAInvariance == TypeOK /\ Inv /\ [Next]_vars => TypeOK' /\ Inv'
PROOF OBVIOUS

(***************************************************************************)
(* The following theorem asserts that the mutual exclusion property is     *)
(* always verified by the system.                                          *)
(***************************************************************************)

=============================================================================
