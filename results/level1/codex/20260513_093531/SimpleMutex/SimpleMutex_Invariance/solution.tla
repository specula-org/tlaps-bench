----------------------------- MODULE SimpleMutex_Invariance -----------------------------
EXTENDS Integers, TLAPS

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
VARIABLES trying, pc

vars == << trying, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ trying = [i \in {0,1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "a"]

a(self) == /\ pc[self] = "a"
           /\ trying' = [trying EXCEPT ![self] = TRUE]
           /\ pc' = [pc EXCEPT ![self] = "b"]

b(self) == /\ pc[self] = "b"
           /\ ~trying[1 - self]
           /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED trying

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED trying

p(self) == a(self) \/ b(self) \/ cs(self)

Next == (\E self \in {0,1}: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

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

THEOREM Invariance == TypeOK /\ Inv /\ Next => TypeOK' /\ Inv'
PROOF
  <1>1. ASSUME TypeOK /\ Inv /\ Next
        PROVE TypeOK' /\ Inv'
    <2>1. CASE \E self \in {0,1}: p(self)
      <3>1. PICK self \in {0,1}: p(self) BY <2>1
      <3>2. CASE a(self)
        <4>1. TypeOK'
          BY <1>1, <3>1, <3>2 DEF TypeOK, a, SMT
        <4>2. Inv'
          BY <1>1, <3>1, <3>2 DEF Inv, TypeOK, a, SMT
        <4>3. QED BY <4>1, <4>2
      <3>3. CASE b(self)
        <4>1. TypeOK'
          BY <1>1, <3>1, <3>3 DEF TypeOK, b, SMT
        <4>2. Inv'
          BY <1>1, <3>1, <3>3 DEF Inv, TypeOK, b, SMT
        <4>3. QED BY <4>1, <4>2
      <3>4. CASE cs(self)
        <4>1. TypeOK'
          BY <1>1, <3>1, <3>4 DEF TypeOK, cs, SMT
        <4>2. Inv'
          BY <1>1, <3>1, <3>4 DEF Inv, TypeOK, cs, SMT
        <4>3. QED BY <4>1, <4>2
      <3>5. QED BY <3>1, <3>2, <3>3, <3>4 DEF p
    <2>2. CASE (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
      <3>1. TypeOK'
        BY <1>1, <2>2 DEF TypeOK, vars, SMT
      <3>2. Inv'
        BY <1>1, <2>2 DEF Inv, vars, SMT
      <3>3. QED BY <3>1, <3>2
    <2>3. QED BY <1>1, <2>1, <2>2 DEF Next, SMT
  <1>2. QED BY <1>1

=============================================================================
