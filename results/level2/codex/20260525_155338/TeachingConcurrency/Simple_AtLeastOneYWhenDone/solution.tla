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
  /\ x \in [ProcSet -> {0, 1}]
  /\ y \in [ProcSet -> {0, 1}]
  /\ pc \in [ProcSet -> {"s1", "s2", "Done"}]

XWritten == \A i \in ProcSet: pc[i] \in {"s2", "Done"} => x[i] = 1

IndInv == TypeOK /\ XWritten /\ AtLeastOneYWhenDone

LEMMA ZeroInProcSet == 0 \in ProcSet
PROOF BY NIsInNat, SMT DEF ProcSet

LEMMA TypeOKInit == Init => TypeOK
PROOF BY SMT DEF Init, TypeOK, ProcSet

LEMMA XWrittenInit == Init => XWritten
PROOF BY SMT DEF Init, XWritten, ProcSet

LEMMA AtLeastOneInit == Init => AtLeastOneYWhenDone
PROOF BY ZeroInProcSet, SMT DEF Init, AtLeastOneYWhenDone, ProcSet

LEMMA IndInvInit == Init => IndInv
PROOF BY TypeOKInit, XWrittenInit, AtLeastOneInit DEF IndInv

LEMMA TypeOKS1 ==
  ASSUME NEW self \in ProcSet
  PROVE  TypeOK /\ s1(self) => TypeOK'
PROOF BY SMT DEF TypeOK, s1

LEMMA TypeOKS2 ==
  ASSUME NEW self \in ProcSet
  PROVE  TypeOK /\ s2(self) => TypeOK'
PROOF BY ModInRange, SMT DEF TypeOK, s2, ProcSet

LEMMA TypeOKTerminating == TypeOK /\ Terminating => TypeOK'
PROOF BY SMT DEF TypeOK, Terminating, vars

LEMMA TypeOKUnchanged == TypeOK /\ UNCHANGED vars => TypeOK'
PROOF BY SMT DEF TypeOK, vars

LEMMA TypeOKNext == TypeOK /\ [Next]_vars => TypeOK'
PROOF BY TypeOKS1, TypeOKS2, TypeOKTerminating, TypeOKUnchanged, SMT
  DEF Next, Proc, ProcSet, vars

LEMMA XWrittenS1 ==
  ASSUME NEW self \in ProcSet
  PROVE  TypeOK /\ XWritten /\ s1(self) => XWritten'
PROOF BY SMT DEF TypeOK, XWritten, s1

LEMMA XWrittenS2 ==
  ASSUME NEW self \in ProcSet
  PROVE  TypeOK /\ XWritten /\ s2(self) => XWritten'
PROOF BY SMT DEF TypeOK, XWritten, s2

LEMMA XWrittenTerminating == TypeOK /\ XWritten /\ Terminating => XWritten'
PROOF BY SMT DEF TypeOK, XWritten, Terminating, vars

LEMMA XWrittenUnchanged == TypeOK /\ XWritten /\ UNCHANGED vars => XWritten'
PROOF BY SMT DEF TypeOK, XWritten, vars

LEMMA XWrittenNext == TypeOK /\ XWritten /\ [Next]_vars => XWritten'
PROOF BY XWrittenS1, XWrittenS2, XWrittenTerminating, XWrittenUnchanged, SMT
  DEF Next, Proc, ProcSet, vars

LEMMA AtLeastOneS1 ==
  ASSUME NEW self \in ProcSet
  PROVE  IndInv /\ s1(self) => AtLeastOneYWhenDone'
PROOF BY SMT DEF IndInv, TypeOK, XWritten, AtLeastOneYWhenDone, s1, ProcSet

LEMMA AtLeastOneS2 ==
  ASSUME NEW self \in ProcSet
  PROVE  IndInv /\ s2(self) => AtLeastOneYWhenDone'
PROOF BY ModInRange, SMT
  DEF IndInv, TypeOK, XWritten, AtLeastOneYWhenDone, s2, ProcSet

LEMMA AtLeastOneTerminating == IndInv /\ Terminating => AtLeastOneYWhenDone'
PROOF BY SMT DEF IndInv, AtLeastOneYWhenDone, Terminating, vars

LEMMA AtLeastOneUnchanged == IndInv /\ UNCHANGED vars => AtLeastOneYWhenDone'
PROOF BY SMT DEF IndInv, AtLeastOneYWhenDone, vars

LEMMA AtLeastOneNext == IndInv /\ [Next]_vars => AtLeastOneYWhenDone'
PROOF BY AtLeastOneS1, AtLeastOneS2, AtLeastOneTerminating, AtLeastOneUnchanged, SMT
  DEF Next, Proc, ProcSet, vars

LEMMA IndInvNext == IndInv /\ [Next]_vars => IndInv'
PROOF BY TypeOKNext, XWrittenNext, AtLeastOneNext DEF IndInv

THEOREM Spec => []AtLeastOneYWhenDone
PROOF
  <1>1. Spec => []IndInv
    BY IndInvInit, IndInvNext, PTL DEF Spec
  <1>2. IndInv => AtLeastOneYWhenDone
    BY DEF IndInv
  <1>3. []IndInv => []AtLeastOneYWhenDone
    BY <1>2, PTL
  <1> QED
    BY <1>1, <1>3
=============================================================================
