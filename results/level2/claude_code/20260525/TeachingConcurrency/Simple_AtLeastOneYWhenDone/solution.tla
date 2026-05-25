------------------------------- MODULE Simple_AtLeastOneYWhenDone -------------------------------
(*
See the paper "Teaching Concurrency" by Leslie Lamport for the problem
(https://www.microsoft.com/en-us/research/uploads/prod/2016/12/Teaching-Concurrency.pdf).

See also the StackOverflow post "What is the inductive invariant of the simple concurrent program?" 
(https://stackoverflow.com/q/24989756/1833118).

See the answer (https://stackoverflow.com/a/46108331/1833118) to the post above 
for the TLA+ specification and TLAPS proof.
*)
EXTENDS Integers, TLAPS
------------------------------------------------------------------------------
CONSTANTS N \* the number of processes
------------------------------------------------------------------------------
(*
--algorithm Simple

variables
    x = [i \in 0 .. N-1 |-> 0];
    y = [i \in 0 .. N-1 |-> 0];

process Proc \in 0 .. N-1 
begin
    s1: x[self] := 1;
    s2: y[self] := x[(self - 1) % N]
end process

end algorithm
*)
------------------------------------------------------------------------------
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0 .. N-1)

Init == (* Global variables *)
        /\ x = [i \in 0 .. N-1 |-> 0]
        /\ y = [i \in 0 .. N-1 |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

Proc(self) == s1(self) \/ s2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0 .. N-1: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
------------------------------------------------------------------------------
AtLeastOneYWhenDone == (\A i \in 0 .. N-1 : pc[i] = "Done") => \E i \in 0 .. N-1 : y[i] = 1

TypeOK == 
    /\ x \in [0 .. N-1 -> {0, 1}]
    /\ y \in [0 .. N-1 -> {0, 1}]
    /\ pc \in [ProcSet -> {"s1", "s2", "Done"}]

Inv == 
    /\ TypeOK
    /\ \A i \in 0 .. N-1 : (pc[i] \in {"s2", "Done"} => x[i] = 1)
    /\ AtLeastOneYWhenDone
------------------------------------------------------------------------------
ASSUME NIsInNat == N \in Nat \ {0}       

\* TLAPS doesn't know this property of modulus operator
AXIOM ModInRange == \A i \in 0 .. N-1: (i-1) % N \in 0 .. N-1

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
<1> USE NIsInNat
<1>1. TypeOK
  BY DEF Init, TypeOK, ProcSet
<1>2. \A i \in 0 .. N-1 : (pc[i] \in {"s2", "Done"} => x[i] = 1)
  BY DEF Init, ProcSet
<1>3. AtLeastOneYWhenDone
  <2>1. 0 \in 0 .. N-1  BY NIsInNat
  <2>2. pc[0] = "s1"  BY <2>1 DEF Init, ProcSet
  <2>3. ~(\A i \in 0 .. N-1 : pc[i] = "Done")  BY <2>1, <2>2
  <2> QED  BY <2>3 DEF AtLeastOneYWhenDone
<1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA InvNext == Inv /\ [Next]_vars => Inv'
<1> USE NIsInNat
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF Inv, TypeOK, AtLeastOneYWhenDone, vars
<1>2. CASE Terminating
  BY <1>2 DEF Terminating, Inv, TypeOK, AtLeastOneYWhenDone, vars
<1>3. CASE \E self \in 0 .. N-1 : Proc(self)
  <2> SUFFICES ASSUME NEW self \in 0 .. N-1, Proc(self) PROVE Inv'  BY <1>3
  <2>x. x \in [0 .. N-1 -> {0, 1}]  BY DEF Inv, TypeOK
  <2>y. y \in [0 .. N-1 -> {0, 1}]  BY DEF Inv, TypeOK
  <2>p. pc \in [0 .. N-1 -> {"s1", "s2", "Done"}]  BY DEF Inv, TypeOK, ProcSet
  <2>1. CASE s1(self)
    <3>x. x' = [x EXCEPT ![self] = 1]  BY <2>1 DEF s1
    <3>p. pc' = [pc EXCEPT ![self] = "s2"]  BY <2>1 DEF s1
    <3>1. TypeOK'
      <4>1. x' \in [0 .. N-1 -> {0, 1}]  BY <2>x, <3>x
      <4>2. pc' \in [ProcSet -> {"s1", "s2", "Done"}]  BY <2>p, <3>p DEF ProcSet
      <4>3. y' = y  BY <2>1 DEF s1
      <4> QED  BY <4>1, <4>2, <4>3, <2>y DEF TypeOK
    <3>2. \A i \in 0 .. N-1 : (pc'[i] \in {"s2", "Done"} => x'[i] = 1)
      <4> SUFFICES ASSUME NEW i \in 0 .. N-1, pc'[i] \in {"s2", "Done"}
                   PROVE  x'[i] = 1
        OBVIOUS
      <4>1. CASE i = self
        BY <4>1, <3>x, <2>x
      <4>2. CASE i # self
        <5>1. pc'[i] = pc[i]  BY <4>2, <3>p, <2>p
        <5>2. x'[i] = x[i]    BY <4>2, <3>x, <2>x
        <5>3. pc[i] \in {"s2", "Done"}  BY <5>1
        <5>4. x[i] = 1  BY <5>3 DEF Inv
        <5> QED  BY <5>2, <5>4
      <4> QED  BY <4>1, <4>2
    <3>3. AtLeastOneYWhenDone'
      <4>1. pc'[self] = "s2"  BY <3>p, <2>p
      <4>2. ~(\A i \in 0 .. N-1 : pc'[i] = "Done")  BY <4>1
      <4> QED  BY <4>2 DEF AtLeastOneYWhenDone
    <3> QED  BY <3>1, <3>2, <3>3 DEF Inv
  <2>2. CASE s2(self)
    <3>y. y' = [y EXCEPT ![self] = x[(self - 1) % N]]  BY <2>2 DEF s2
    <3>p. pc' = [pc EXCEPT ![self] = "Done"]  BY <2>2 DEF s2
    <3>x. x' = x  BY <2>2 DEF s2
    <3>m. (self - 1) % N \in 0 .. N-1  BY ModInRange
    <3>1. TypeOK'
      <4>1. x[(self - 1) % N] \in {0, 1}  BY <3>m, <2>x
      <4>2. y' \in [0 .. N-1 -> {0, 1}]  BY <4>1, <3>y, <2>y
      <4>3. pc' \in [ProcSet -> {"s1", "s2", "Done"}]  BY <2>p, <3>p DEF ProcSet
      <4> QED  BY <4>2, <4>3, <3>x, <2>x DEF TypeOK
    <3>2. \A i \in 0 .. N-1 : (pc'[i] \in {"s2", "Done"} => x'[i] = 1)
      <4> SUFFICES ASSUME NEW i \in 0 .. N-1, pc'[i] \in {"s2", "Done"}
                   PROVE  x'[i] = 1
        OBVIOUS
      <4>1. CASE i = self
        <5>1. pc[self] = "s2"  BY <2>2 DEF s2
        <5>2. x[self] = 1  BY <5>1 DEF Inv
        <5> QED  BY <4>1, <5>2, <3>x
      <4>2. CASE i # self
        <5>1. pc'[i] = pc[i]  BY <4>2, <3>p, <2>p
        <5>2. x[i] = 1  BY <5>1 DEF Inv
        <5> QED  BY <5>2, <3>x
      <4> QED  BY <4>1, <4>2
    <3>3. AtLeastOneYWhenDone'
      <4> SUFFICES ASSUME \A i \in 0 .. N-1 : pc'[i] = "Done"
                   PROVE  \E i \in 0 .. N-1 : y'[i] = 1
        BY DEF AtLeastOneYWhenDone
      <4>2. pc[(self - 1) % N] \in {"s2", "Done"}
        <5>1. CASE (self - 1) % N = self
          <6>1. pc[self] = "s2"  BY <2>2 DEF s2
          <6> QED  BY <5>1, <6>1
        <5>2. CASE (self - 1) % N # self
          <6>1. pc'[(self - 1) % N] = "Done"  BY <3>m
          <6>2. pc'[(self - 1) % N] = pc[(self - 1) % N]  BY <5>2, <3>m, <3>p, <2>p
          <6> QED  BY <6>1, <6>2
        <5> QED  BY <5>1, <5>2
      <4>3. x[(self - 1) % N] = 1  BY <3>m, <4>2 DEF Inv
      <4>4. y'[self] = x[(self - 1) % N]  BY <3>y, <2>y
      <4>5. y'[self] = 1  BY <4>3, <4>4
      <4> QED  BY <4>5
    <3> QED  BY <3>1, <3>2, <3>3 DEF Inv
  <2> QED  BY <2>1, <2>2 DEF Proc
<1> QED  BY <1>1, <1>2, <1>3 DEF Next

THEOREM Spec => []AtLeastOneYWhenDone
<1>1. Init => Inv  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'  BY InvNext
<1>3. Inv => AtLeastOneYWhenDone  BY DEF Inv
<1>4. Spec => []Inv  BY <1>1, <1>2, PTL DEF Spec
<1> QED  BY <1>4, <1>3, PTL
=============================================================================
\* Modification History
\* Last modified Wed Aug 07 17:32:20 CST 2019 by hengxin
\* Created Fri Aug 02 13:28:48 CST 2019 by hengxin