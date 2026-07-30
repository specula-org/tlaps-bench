------------------------------- MODULE Peterson_RefinementScaffold -------------------------------

(*****************************************************************************)
(* This module contains the specification for Peterson's Algorithm, taken    *)
(* from the "Parallel Programming" course taught at ULiège.                  *)
(* The invariant `Inv` is the one presented in the course augmented by a     *)
(* clause representing mutual exclusion of the critical section              *)
(* A proof is given to show that `Inv` is inductive.                         *)
(* Moreover the refinement from Peterson to the abstract lock is also proven.*)
(*****************************************************************************)

EXTENDS PetersonModel

(*
--algorithm Peterson{
    variables
      c = [self \in ProcSet |-> FALSE],
      turn = 1;

    process(proc \in 1..2){
a0:   while(TRUE){
        skip;
a1:     c[self] := TRUE;
a2:     turn := Other(self);
a3:     await ~c[Other(self)] \/ turn = self;
cs:     skip;
a4:     c[self] := FALSE;
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1d547bc3" /\ chksum(tla) = "8de86c82")

\* END TRANSLATION 

TypeOK ==
  /\ c \in [ProcSet -> BOOLEAN]
  /\ turn \in ProcSet
  /\ pc \in [ProcSet -> {"a0", "a1", "a2", "a3", "cs", "a4"}]

lockcs(i) ==
  pc[i] \in {"cs", "a4"}
Inv ==
  /\ \A p \in ProcSet : c[p] <=> pc[p] \in {"a2", "a3", "cs", "a4"}
  /\ \A p \in ProcSet : pc[p] \in {"cs", "a4"} 
      => (turn = p \/ pc[Other(p)] \in {"a0", "a1", "a2"})
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))

pc_translation(label) ==
  CASE (label = "a0") -> "l0"
    [] (label \in {"a1", "a2", "a3"}) -> "l1"
    [] (label \in {"cs"}) -> "cs"
    [] (label \in {"a4"}) -> "l2"

lock_translation == IF \E p \in ProcSet : pc[p] \in {"cs", "a4"} THEN 0 ELSE 1

L == INSTANCE Lock
     WITH pc <- [p \in ProcSet |-> pc_translation(pc[p])], 
     lock <- lock_translation
LSpec == L!Spec

LEMMA Typing == Spec => []TypeOK
PROOF OMITTED

THEOREM IndInvariant == Spec => []Inv
PROOF OMITTED

=============================================================================
