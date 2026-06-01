----------------------------- MODULE SimpleMutex_Initialization -----------------------------
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
PROOF
  <1>1. SUFFICES ASSUME Init PROVE TypeOK /\ Inv OBVIOUS
  <1>2. trying = [i \in {0,1} |-> FALSE] BY <1>1 DEF Init
  <1>3. pc = [self \in ProcSet |-> CASE self \in {0,1} -> "a"] BY <1>1 DEF Init
  <1>4. trying \in [{0,1} -> BOOLEAN]
    BY <1>2
  <1>5. pc \in [{0,1} -> {"a", "b", "cs", "Done"}]
    BY <1>3 DEF ProcSet
  <1>6. TypeOK BY <1>4, <1>5 DEF TypeOK
  <1>7. Inv
    <2>1. SUFFICES ASSUME NEW i \in {0,1}
                    PROVE  /\ pc[i] \in {"b", "cs"} => trying[i]
                           /\ pc[i] = "cs" => pc[1-i] # "cs"
      BY DEF Inv
    <2>2. pc[i] = "a" BY <1>3, <2>1 DEF ProcSet
    <2>3. pc[i] \notin {"b", "cs"} BY <2>2
    <2>4. pc[i] # "cs" BY <2>2
    <2>5. QED BY <2>3, <2>4
  <1>8. QED BY <1>6, <1>7

=============================================================================
