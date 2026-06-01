---------------------- MODULE TwoPhase_Implementation -----------------------
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
(* Our proof requires the following simple fact about the modulus operator *)
(* % .  It is proved using a decision procedure, as explained in the       *)
(* comments in the TLAProofRules module.                                   *)
(*                                                                         *)
(* Often, a proof requires a simple mathematical fact that cannot be       *)
(* deduced so easily by the Proof System.  In fact, the Proof System may   *)
(* not even know some basic mathematical facts needed to prove it.         *)
(* Proving the needed fact is a fun exercise for those who enjoy that sort *)
(* of thing.  It's painful for the rest of us.  Eventually, we will have a *)
(* library with lots of useful facts that you can import.  But such a      *)
(* library is unlikely ever to contain all the simple mathematical         *)
(* theoresm that you'll ever need.                                         *)
(*                                                                         *)
(* We are primarily interested in making the Proof System useful to people *)
(* who want to prove things about algorithms and systems, not for those    *)
(* who want to prove theorems of mathematics.  (We hope that the Proof     *)
(* System will be good for doing those proofs too, but we are not doing    *)
(* anything special to achieve this.)  We expect that most users will      *)
(* simply assume these mathematical facts.  However, it's dangerous to     *)
(* assume the truth of a theorem without checking it in some way.  It's    *)
(* easy to make a mistake and write a false theorem, and assuming a false  *)
(* theorem could allow you to prove other false theorems.  So, you should  *)
(* use the TLC model checker to check any fact that you assume.  In most   *)
(* cases, TLC won't be able to check the actual theorem.  But it should be *)
(* able to do a good enough job to catch errors.  For example, TLC can't   *)
(* check that a theorem is true for all integers.  However, in practice we *)
(* expect that you will be able to check it for a large enough subset of   *)
(* the integers to gain sufficient confidence that the theorem really is   *)
(* true.  In this case, TLC could check the actual theorem.                *)
(***************************************************************************)
THEOREM Mod2 == \A i \in {0,1} : /\ (i + 1) % 2 = 1 - i
                                 /\ (i + 0) % 2 = i
  PROOF OMITTED

THEOREM Implementation == Spec => A!Spec
PROOF
  <1>1. Init => A!Init
    BY DEF Init, A!Init, vBar
  <1>2. Init => Inv
    BY DEF Init, Inv
  <1>3. Inv /\ [Next]_<<p, c, x>> => Inv'
    <2>1. ASSUME Inv, [Next]_<<p, c, x>>
          PROVE  Inv'
      <3>1. CASE Next
        <4>1. CASE ProducerStep
          <5>1. p' \in {0,1}
            BY <2>1, <4>1, Mod2 DEF Inv, ProducerStep
          <5>2. c' \in {0,1}
            BY <2>1, <4>1 DEF Inv, ProducerStep
          <5>. QED BY <5>1, <5>2 DEF Inv
        <4>2. CASE ConsumerStep
          <5>1. p' \in {0,1}
            BY <2>1, <4>2 DEF Inv, ConsumerStep
          <5>2. c' \in {0,1}
            BY <2>1, <4>2, Mod2 DEF Inv, ConsumerStep
          <5>. QED BY <5>1, <5>2 DEF Inv
        <4>. QED BY <3>1, <4>1, <4>2 DEF Next
      <3>2. CASE UNCHANGED <<p, c, x>>
        BY <2>1, <3>2 DEF Inv
      <3>. QED BY <2>1, <3>1, <3>2
    <2>. QED BY <2>1
  <1>4. Inv /\ [Next]_<<p, c, x>> => [A!Next]_<<vBar, x>>
    <2>1. ASSUME Inv, [Next]_<<p, c, x>>
          PROVE  [A!Next]_<<vBar, x>>
      <3>1. CASE Next
        <4>1. CASE ProducerStep
          <5>1. vBar = 0
            BY <2>1, <4>1, Mod2 DEF Inv, ProducerStep, vBar
          <5>2. vBar' = 1
            BY <2>1, <4>1, Mod2 DEF Inv, ProducerStep, vBar
          <5>3. A!Next
            <6>1. vBar' = (vBar + 1) % 2
              BY <5>1, <5>2, Mod2
            <6>2. XAct(vBar, x, x')
              BY <4>1, <5>1 DEF ProducerStep
            <6>. QED BY <6>1, <6>2 DEF A!Next
          <5>. QED BY <5>3
        <4>2. CASE ConsumerStep
          <5>1. vBar = 1
            BY <2>1, <4>2, Mod2 DEF Inv, ConsumerStep, vBar
          <5>2. vBar' = 0
            BY <2>1, <4>2, Mod2 DEF Inv, ConsumerStep, vBar
          <5>3. A!Next
            <6>1. vBar' = (vBar + 1) % 2
              BY <5>1, <5>2, Mod2
            <6>2. XAct(vBar, x, x')
              BY <4>2, <5>1 DEF ConsumerStep
            <6>. QED BY <6>1, <6>2 DEF A!Next
          <5>. QED BY <5>3
        <4>. QED BY <3>1, <4>1, <4>2 DEF Next
      <3>2. CASE UNCHANGED <<p, c, x>>
        <4>1. UNCHANGED <<vBar, x>>
          BY <3>2 DEF vBar
        <4>. QED BY <4>1
      <3>. QED BY <2>1, <3>1, <3>2
    <2>. QED BY <2>1
  <1>. QED BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec, A!Spec

==============================================================
