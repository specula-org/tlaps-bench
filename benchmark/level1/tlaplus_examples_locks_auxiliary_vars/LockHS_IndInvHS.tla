---- MODULE LockHS_IndInvHS ----
EXTENDS Integers, NaturalsInduction, TLAPS
(* ---- Content from module Lock ---- *)

(*****************************************************************************)
(* This module contains the specification of an abstract lock.               *)
(* The proof for mutual exclusion is also detailed.                          *)
(*****************************************************************************)


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
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ lock = 1
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in 1..2: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [ProcSet -> {"l0", "l1", "cs", "l2"}]

lockcs(i) ==
  pc[i] \in {"cs", "l2"}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0

-------------------------------------------------------------------------------

LEMMA Typing == Spec => []TypeOK
  PROOF OMITTED

THEOREM MutualExclusion == Spec => []LockInv
  PROOF OMITTED

VARIABLE h_turn
NoHistoryChange(A) == A /\ UNCHANGED h_turn

\* Stuttering variable
VARIABLE s
INSTANCE Stuttering

\* This theorem justifies the validity of the introduced stuttering variable
\* in definition l1HS
THEOREM StutterConstantCondition(1..2, 1, LAMBDA j : j-1)
  PROOF OMITTED

-------------------------------------------------------------------------------

Other(p) == IF p = 1 THEN 2 ELSE 1 

InitHS == Init /\ (h_turn = 1) /\ (s = top)

\* Adding 2 stuttering steps after an l1(self) transition
\* Updating the history variable during the right stutter step
l1HS(self) == 
  /\ PostStutter(l1(self), "l1", self, 1, 2, LAMBDA j : j-1)
  /\ h_turn' = IF s' # top THEN IF s'.val = 1 THEN Other(self)
                                              ELSE h_turn
                           ELSE h_turn

procHS(self) == 
  \/ NoStutter(NoHistoryChange(l0(self)))
  \/ l1HS(self)
  \/ NoStutter(NoHistoryChange(cs(self)))
  \/ NoStutter(NoHistoryChange(l2(self)))

NextHS == (\E self \in 1..2: procHS(self))

SpecHS == InitHS /\ [][NextHS]_<<vars, h_turn, s>>

-------------------------------------------------------------------------------

TypeOKHS == 
  /\ TypeOK
  /\ h_turn \in 1..2
  /\ s \in {top} \cup [id : {"l1"}, ctxt : {1, 2}, val : 1..2]

InvHS == 
  /\ \A p \in ProcSet : 
    /\ IF s # top THEN s.ctxt = p ELSE FALSE
    => pc[p] = "cs"
  /\ \A p \in ProcSet :
    \/ pc[p] = "l2"
    \/ pc[p] = "cs" /\ s = top
    \/ IF s # top THEN s.ctxt = p /\ s.val = 1 ELSE FALSE
    => h_turn = Other(p)

pc_translation(self, label, stutter) == 
  CASE (label = "l0") -> "a0"
    [] (label = "l1") -> "a1"
    [] (label = "l2") -> "a4"
    [] (label = "cs") -> IF stutter = top THEN "cs"
                         ELSE IF stutter.ctxt # self THEN "cs"
                         ELSE IF stutter.val = 2 THEN "a2"
                         ELSE IF stutter.val = 1 THEN "a3"
                         ELSE "error"
c_translation(alt_label) == 
  alt_label \in {"a2", "a3", "cs", "a4"}

P == INSTANCE Peterson WITH
      pc <- [p \in ProcSet |-> pc_translation(p, pc[p], s)],
      c <- [p \in ProcSet |-> c_translation(pc_translation(p, pc[p], s))],
      turn <- h_turn
PSpec == P!Spec

-------------------------------------------------------------------------------

(*****************************************************************************)
(* Proofs using stuttering variables can be quite complicated as the backend *)
(* solvers can be quite overwhelmed by the different transitions made        *)
(* possible by the PostStutter clauses.                                      *)
(* The easiest way to complete such proofs seems to be the extraction of     *)
(* all relevant information in a first step and then refer to that step      *)
(* instead of the expanded PostStutter.                                      *)
(*****************************************************************************)

LEMMA TypingHS == SpecHS => []TypeOKHS
  PROOF OMITTED

LEMMA AddingVariables == SpecHS => Spec
  PROOF OMITTED

LEMMA MutualExclusionHS == SpecHS => []LockInv
  PROOF OMITTED

LEMMA IndInvHS == SpecHS => []InvHS
PROOF OBVIOUS

========================================