---------------------- MODULE TwoPhase -----------------------
(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but    *)
(* very important hardware protocol by which a Producer process and a      *)
(* Consumer process alternately perform actions, with the Producer going   *)
(* first.  The system is pictured as follows:                              *)
(*                                                                         *)
(* `.                                                                      *)
(*     ------------           p          ------------                      *)
(*    |            | -----------------> |            |                     *)
(*    |  Producer  |                    |  Consumer  |                     *)
(*    |            | <----------------- |            |                     *)
(*     ------------           c          ------------    .'                *)
(*                                                                         *)
(*                                                                         *)
(* In the spec, we represent the Producer and Consumer actions the way we  *)
(* represented the actions A_0 and A_1 of the Alternate specification.  We *)
(* then show that this specification implements the Alternate              *)
(* specification under a suitable refinement mapping (substitution for the *)
(* variable v).                                                            *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT XInit(_), XAct(_, _, _)
 
VARIABLE p, c, x

Init == /\ p = 0 
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_<<p, c, x>>


(***************************************************************************)
(* Inv is the invariant that is needed for the proof.                      *)
(***************************************************************************)
Inv == (p \in {0,1}) /\ (c \in {0,1})

(***************************************************************************)
(* We prove that specification Spec implement (implies) the specification  *)
(* obtained by substiting a state function vBar for the variable v, where  *)
(* vBar is defined as follows.                                             *)
(***************************************************************************)
vBar == (p + c) % 2

(***************************************************************************)
(* The following statement imports, for every defined operator D of module *)
(* Alternate, a definition of A!D to equal the definition of D with vBar   *)
(* substituted for v and with the parameters x, XInit, and XAct of this    *)
(* module substituted for the parameters of the same name of module        *)
(* Alternate.  Thus, A!Spec is defined to be the formula Spec of module    *)
(* Alternate with vBar substituted for v.                                  *)
(***************************************************************************)
A == INSTANCE Alternate WITH v <- vBar

(***************************************************************************)
(* The following theorem is a standard proof that one specification        *)
(* implements (the safety part of) another specification under a           *)
(* refinement mapping.  In fact, the temporal leaf proofs will be exactly  *)
(* the same one-liners for every such proof.  In realistic example, the    *)
(* non-temporal leaf proofs will be replaced by fairly long structured     *)
(* proofs--especially the two substeps numbered <2>2.                      *)
(***************************************************************************)
THEOREM Implementation == Spec => A!Spec
<1>1. Spec => []Inv
  <2>1. Init => Inv
    BY DEF Init, Inv
  <2>2. Inv /\ [Next]_<<p, c, x>> => Inv'
    BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep
  <2>. QED
    BY <2>1, <2>2, PTL DEF Spec
<1>2. QED
  <2>1. Init => A!Init
    BY Z3 DEF Init, A!Init, vBar
  <2>2. Inv /\ [Next]_<<p, c, x>>  => [A!Next]_<<vBar, x>>
    BY Z3 DEF Inv, Next, ProducerStep, ConsumerStep, A!Next, vBar
  <2>3. []Inv /\ [][Next]_<<p, c, x>>  => [][A!Next]_<<vBar, x>>
    BY <2>1, <2>2, PTL
  <2>. QED
    BY <2>1, <2>3, <1>1, PTL DEF Spec, A!Spec
  
==============================================================
\* Generated at Sat Oct 31 03:15:55 PDT 2009
