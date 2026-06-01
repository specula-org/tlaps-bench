----------------------------- MODULE SimpleMutex_line140 -----------------------------
EXTENDS Integers, TLAPS

VARIABLES trying, pc

vars == << trying, pc >>

ProcSet == ({0,1})

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
           \/ 
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

TypeOK ==
  /\ trying \in [{0,1} -> BOOLEAN]
  /\ pc \in [{0,1} -> {"a", "b", "cs", "Done"}]

Inv == \A i \in {0,1} :
          /\ pc[i] \in {"b", "cs"} => trying[i]
          /\ pc[i] = "cs" => pc[1-i] # "cs"

LEMMA AStepOK ==
  ASSUME TypeOK, Inv, NEW self \in {0,1}, a(self)
  PROVE  TypeOK' /\ Inv'
PROOF
  BY SMT DEF TypeOK, Inv, a

LEMMA BStepOK ==
  ASSUME TypeOK, Inv, NEW self \in {0,1}, b(self)
  PROVE  TypeOK' /\ Inv'
PROOF
  BY SMT DEF TypeOK, Inv, b

LEMMA CSStepOK ==
  ASSUME TypeOK, Inv, NEW self \in {0,1}, cs(self)
  PROVE  TypeOK' /\ Inv'
PROOF
  BY SMT DEF TypeOK, Inv, cs

LEMMA StutterOK ==
  ASSUME TypeOK, Inv, UNCHANGED vars
  PROVE  TypeOK' /\ Inv'
PROOF
  BY SMT DEF TypeOK, Inv, vars

THEOREM
  ASSUME TypeOK, Inv, Next
  PROVE  TypeOK' /\ Inv'
PROOF
  <1>1. CASE \E self \in {0,1} : p(self)
    <2>1. PICK self \in {0,1} : p(self) BY <1>1
    <2>2. QED BY <2>1, AStepOK, BStepOK, CSStepOK DEF p
  <1>2. CASE (\A self \in ProcSet : pc[self] = "Done") /\ UNCHANGED vars
    BY <1>2, StutterOK DEF ProcSet
  <1>3. QED BY <1>1, <1>2 DEF Next
----------------------------------------------------------------------

=============================================================================
