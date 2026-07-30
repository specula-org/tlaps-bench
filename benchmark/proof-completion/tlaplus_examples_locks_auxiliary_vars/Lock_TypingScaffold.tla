--------------------------------- MODULE Lock_TypingScaffold ---------------------------------

(*****************************************************************************)
(* This module contains the specification of an abstract lock.               *)
(* The proof for mutual exclusion is also detailed.                          *)
(*****************************************************************************)

EXTENDS LockModel

(*
--algorithm Lock{
    variables lock = 1;
    
    macro Lock(l){
      await l = 1;
      l := 0;
    }
    
    macro Unlock(l){
      l := 1;
    }
  
    process(proc \in 1..2){
l0:   while(TRUE){
        skip; \* non-critical section
l1:     Lock(lock);
cs:     skip; \* critical section
l2:     Unlock(lock);
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f820ffbb" /\ chksum(tla) = "24b4f3dd")

\* END TRANSLATION 

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [ProcSet -> {"l0", "l1", "cs", "l2"}]

lockcs(i) ==
  pc[i] \in {"cs", "l2"}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0

=============================================================================
