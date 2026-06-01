------------------------------- MODULE Simple_AtLeastOneYWhenDone -------------------------------

EXTENDS Integers, TLAPS
------------------------------------------------------------------------------
CONSTANTS N
------------------------------------------------------------------------------

------------------------------------------------------------------------------

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0 .. N-1)

Init ==
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

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0 .. N-1: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
AtLeastOneYWhenDone == (\A i \in 0 .. N-1 : pc[i] = "Done") => \E i \in 0 .. N-1 : y[i] = 1

------------------------------------------------------------------------------
ASSUME NIsInNat == N \in Nat \ {0}

AXIOM ModInRange == \A i \in 0 .. N-1: (i-1) % N \in 0 .. N-1

TypeOK ==
  /\ x \in [0..N-1 -> {0, 1}]
  /\ y \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"s1", "s2", "Done"}]

IndInv ==
  /\ TypeOK
  /\ \A i \in 0..N-1: pc[i] = "s1" => x[i] = 0
  /\ \A i \in 0..N-1: pc[i] \in {"s2", "Done"} => x[i] = 1
  /\ (\A i \in 0..N-1: pc[i] \in {"s2", "Done"}) =>
       ((\E j \in 0..N-1: y[j] = 1) \/ (\E j \in 0..N-1: pc[j] = "s2"))

LEMMA InitImpliesIndInv == Init => IndInv
  BY NIsInNat DEF Init, IndInv, TypeOK, ProcSet

LEMMA S1PreservesIndInv ==
  ASSUME IndInv, NEW self \in 0..N-1, s1(self)
  PROVE IndInv'
PROOF
  <1>1. pc[self] = "s1" BY DEF s1
  <1>2. x[self] = 0 BY <1>1 DEF IndInv
  <1>3. x' = [x EXCEPT ![self] = 1] BY DEF s1
  <1>4. pc' = [pc EXCEPT ![self] = "s2"] BY DEF s1
  <1>5. y' = y BY DEF s1
  <1>6. TypeOK BY DEF IndInv
  <1>7. x' \in [0..N-1 -> {0, 1}]
    BY <1>3, <1>6 DEF TypeOK
  <1>8. y' \in [0..N-1 -> {0, 1}]
    BY <1>5, <1>6 DEF TypeOK
  <1>9. pc' \in [0..N-1 -> {"s1", "s2", "Done"}]
    BY <1>4, <1>6 DEF TypeOK
  <1>10. TypeOK' BY <1>7, <1>8, <1>9 DEF TypeOK
  <1>11. \A i \in 0..N-1: pc'[i] = "s1" => x'[i] = 0
    <2>1. TAKE i \in 0..N-1
    <2>2. ASSUME pc'[i] = "s1" PROVE x'[i] = 0
      <3>1. CASE i = self
        <4>1. pc'[self] = "s2" BY <1>4, <1>6 DEF TypeOK
        <4>2. QED BY <4>1, <3>1, <2>2
      <3>2. CASE i # self
        <4>1. pc'[i] = pc[i] BY <3>2, <1>4, <1>6 DEF TypeOK
        <4>2. x'[i] = x[i] BY <3>2, <1>3, <1>6 DEF TypeOK
        <4>3. pc[i] = "s1" BY <4>1, <2>2
        <4>4. x[i] = 0 BY <4>3 DEF IndInv
        <4>5. QED BY <4>2, <4>4
      <3>3. QED BY <3>1, <3>2
    <2>3. QED BY <2>2
  <1>12. \A i \in 0..N-1: pc'[i] \in {"s2", "Done"} => x'[i] = 1
    <2>1. TAKE i \in 0..N-1
    <2>2. ASSUME pc'[i] \in {"s2", "Done"} PROVE x'[i] = 1
      <3>1. CASE i = self
        <4>1. x'[self] = 1 BY <1>3, <1>6 DEF TypeOK
        <4>2. QED BY <4>1, <3>1
      <3>2. CASE i # self
        <4>1. pc'[i] = pc[i] BY <3>2, <1>4, <1>6 DEF TypeOK
        <4>2. x'[i] = x[i] BY <3>2, <1>3, <1>6 DEF TypeOK
        <4>3. pc[i] \in {"s2", "Done"} BY <4>1, <2>2
        <4>4. x[i] = 1 BY <4>3 DEF IndInv
        <4>5. QED BY <4>2, <4>4
      <3>3. QED BY <3>1, <3>2
    <2>3. QED BY <2>2
  <1>13. (\A i \in 0..N-1: pc'[i] \in {"s2", "Done"}) =>
            ((\E j \in 0..N-1: y'[j] = 1) \/ (\E j \in 0..N-1: pc'[j] = "s2"))
    <2>1. ASSUME \A i \in 0..N-1: pc'[i] \in {"s2", "Done"}
          PROVE (\E j \in 0..N-1: y'[j] = 1) \/ (\E j \in 0..N-1: pc'[j] = "s2")
      <3>1. pc'[self] = "s2" BY <1>4, <1>6 DEF TypeOK
      <3>2. QED BY <3>1
    <2>2. QED BY <2>1
  <1>14. QED BY <1>10, <1>11, <1>12, <1>13 DEF IndInv

LEMMA S2PreservesIndInv ==
  ASSUME IndInv, NEW self \in 0..N-1, s2(self)
  PROVE IndInv'
PROOF
  <1>1. pc[self] = "s2" BY DEF s2
  <1>2. x[self] = 1 BY <1>1 DEF IndInv
  <1>3. x' = x BY DEF s2
  <1>4. pc' = [pc EXCEPT ![self] = "Done"] BY DEF s2
  <1>5. y' = [y EXCEPT ![self] = x[(self - 1) % N]] BY DEF s2
  <1>6. TypeOK BY DEF IndInv
  <1>mod. (self - 1) % N \in 0..N-1 BY ModInRange
  <1>xrange. x[(self - 1) % N] \in {0, 1} BY <1>mod, <1>6 DEF TypeOK
  <1>7. x' \in [0..N-1 -> {0, 1}]
    BY <1>3, <1>6 DEF TypeOK
  <1>8. y' \in [0..N-1 -> {0, 1}]
    BY <1>5, <1>xrange, <1>6 DEF TypeOK
  <1>9. pc' \in [0..N-1 -> {"s1", "s2", "Done"}]
    BY <1>4, <1>6 DEF TypeOK
  <1>10. TypeOK' BY <1>7, <1>8, <1>9 DEF TypeOK
  <1>11. \A i \in 0..N-1: pc'[i] = "s1" => x'[i] = 0
    <2>1. TAKE i \in 0..N-1
    <2>2. ASSUME pc'[i] = "s1" PROVE x'[i] = 0
      <3>1. CASE i = self
        <4>1. pc'[self] = "Done" BY <1>4, <1>6 DEF TypeOK
        <4>2. QED BY <4>1, <3>1, <2>2
      <3>2. CASE i # self
        <4>1. pc'[i] = pc[i] BY <3>2, <1>4, <1>6 DEF TypeOK
        <4>2. x'[i] = x[i] BY <1>3
        <4>3. pc[i] = "s1" BY <4>1, <2>2
        <4>4. x[i] = 0 BY <4>3 DEF IndInv
        <4>5. QED BY <4>2, <4>4
      <3>3. QED BY <3>1, <3>2
    <2>3. QED BY <2>2
  <1>12. \A i \in 0..N-1: pc'[i] \in {"s2", "Done"} => x'[i] = 1
    <2>1. TAKE i \in 0..N-1
    <2>2. ASSUME pc'[i] \in {"s2", "Done"} PROVE x'[i] = 1
      <3>1. CASE i = self
        <4>1. x'[i] = x[i] BY <1>3
        <4>2. x[i] = 1 BY <1>2, <3>1
        <4>3. QED BY <4>1, <4>2
      <3>2. CASE i # self
        <4>1. pc'[i] = pc[i] BY <3>2, <1>4, <1>6 DEF TypeOK
        <4>2. x'[i] = x[i] BY <1>3
        <4>3. pc[i] \in {"s2", "Done"} BY <4>1, <2>2
        <4>4. x[i] = 1 BY <4>3 DEF IndInv
        <4>5. QED BY <4>2, <4>4
      <3>3. QED BY <3>1, <3>2
    <2>3. QED BY <2>2
  <1>13. (\A i \in 0..N-1: pc'[i] \in {"s2", "Done"}) =>
            ((\E j \in 0..N-1: y'[j] = 1) \/ (\E j \in 0..N-1: pc'[j] = "s2"))
    <2>1. ASSUME \A i \in 0..N-1: pc'[i] \in {"s2", "Done"}
          PROVE (\E j \in 0..N-1: y'[j] = 1) \/ (\E j \in 0..N-1: pc'[j] = "s2")
      <3>1. \A i \in 0..N-1: pc[i] \in {"s2", "Done"}
        <4>1. TAKE i \in 0..N-1
        <4>2. CASE i = self
          BY <1>1, <4>2
        <4>3. CASE i # self
          <5>1. pc'[i] = pc[i] BY <4>3, <1>4, <1>6 DEF TypeOK
          <5>2. pc'[i] \in {"s2", "Done"} BY <2>1
          <5>3. QED BY <5>1, <5>2
        <4>4. QED BY <4>2, <4>3
      <3>2. pc[(self - 1) % N] \in {"s2", "Done"} BY <3>1, <1>mod
      <3>3. x[(self - 1) % N] = 1 BY <3>2, <1>mod DEF IndInv
      <3>4. y'[self] = 1 BY <1>5, <1>6, <3>3 DEF TypeOK
      <3>5. QED BY <3>4
    <2>2. QED BY <2>1
  <1>14. QED BY <1>10, <1>11, <1>12, <1>13 DEF IndInv

LEMMA TerminatingPreservesIndInv ==
  ASSUME IndInv, Terminating
  PROVE IndInv'
PROOF
  <1>1. UNCHANGED vars BY DEF Terminating
  <1>2. x' = x /\ y' = y /\ pc' = pc BY <1>1 DEF vars
  <1>3. QED BY <1>2 DEF IndInv, TypeOK

LEMMA UnchangedPreservesIndInv ==
  ASSUME IndInv, UNCHANGED vars
  PROVE IndInv'
PROOF
  <1>1. x' = x /\ y' = y /\ pc' = pc BY DEF vars
  <1>2. QED BY <1>1 DEF IndInv, TypeOK

LEMMA NextPreservesIndInv ==
  ASSUME IndInv, [Next]_vars
  PROVE IndInv'
PROOF
  <1>1. CASE UNCHANGED vars BY <1>1, UnchangedPreservesIndInv
  <1>2. CASE Next
    <2>1. CASE \E self \in 0..N-1: Proc(self)
      <3>1. PICK self \in 0..N-1: Proc(self) BY <2>1
      <3>2. CASE s1(self) BY <3>1, <3>2, S1PreservesIndInv
      <3>3. CASE s2(self) BY <3>1, <3>3, S2PreservesIndInv
      <3>4. QED BY <3>1, <3>2, <3>3 DEF Proc
    <2>2. CASE Terminating BY <2>2, TerminatingPreservesIndInv
    <2>3. QED BY <1>2, <2>1, <2>2 DEF Next
  <1>3. QED BY <1>1, <1>2

LEMMA Inductive == Spec => []IndInv
PROOF
  <1>1. Init => IndInv BY InitImpliesIndInv
  <1>2. IndInv /\ [Next]_vars => IndInv' BY NextPreservesIndInv
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

LEMMA IndInvImpliesProperty == IndInv => AtLeastOneYWhenDone
PROOF
  <1>1. ASSUME IndInv, \A i \in 0..N-1: pc[i] = "Done"
        PROVE \E i \in 0..N-1: y[i] = 1
    <2>1. \A i \in 0..N-1: pc[i] \in {"s2", "Done"} BY <1>1
    <2>2. (\E j \in 0..N-1: y[j] = 1) \/ (\E j \in 0..N-1: pc[j] = "s2")
      BY <1>1, <2>1 DEF IndInv
    <2>3. ~ (\E j \in 0..N-1: pc[j] = "s2")
      BY <1>1
    <2>4. QED BY <2>2, <2>3
  <1>2. QED BY <1>1 DEF AtLeastOneYWhenDone

THEOREM Spec => []AtLeastOneYWhenDone
PROOF
  <1>1. Spec => []IndInv BY Inductive
  <1>2. IndInv => AtLeastOneYWhenDone BY IndInvImpliesProperty
  <1>3. QED BY <1>1, <1>2, PTL
=============================================================================
