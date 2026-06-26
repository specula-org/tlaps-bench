-------------------------------- MODULE LockHS_AddingVariables --------------------------------

(*****************************************************************************)
(* This module contains the specification of a lock with auxiliary variables.*)
(* 1. A history variable `h_turn` is needed to remember the assignement of   *)
(*    the turn variable used inside the Peterson specification.              *)
(* 2. A stuttering variable `s` is added to force the stuttering of the Lock *)
(*    specification to mimick the 3 steps taken by Peterson to enter the     *)
(*    critical section.                                                      *)
(* With these variables, one can finally refine LockHS to Peterson, giving   *)
(* an equivalence between the Lock and Peterson specifications.              *)
(*                                                                           *)
(* The stuttering is achieved using the Stuttering module created by Leslie  *)
(* Lamport and comes from to the paper "Auxiliary Variables in TLA+".        *)
(* The module used here has been modified, see explanations at the end of    *) 
(* the Stuttering module.                                                    *)
(*****************************************************************************)

EXTENDS LockHS

\* History variable to remember the turn variable

\* Stuttering variable
INSTANCE Stuttering

\* This theorem justifies the validity of the introduced stuttering variable
\* in definition l1HS
THEOREM StutterConstantCondition(1..2, 1, LAMBDA j : j-1)
PROOF OMITTED

\* Adding 2 stuttering steps after an l1(self) transition
\* Updating the history variable during the right stutter step

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
PROOF OBVIOUS

===============================================================================