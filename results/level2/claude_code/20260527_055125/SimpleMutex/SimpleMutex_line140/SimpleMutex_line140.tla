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

LEMMA L_Sub01 == \A i \in {0,1} : (1 - i) \in {0,1} /\ (1 - (1 - i)) = i /\ i # (1 - i)
PROOF
  <1>1. (1 - 0) \in {0,1} /\ (1 - (1 - 0)) = 0 /\ 0 # (1 - 0)
    OBVIOUS
  <1>2. (1 - 1) \in {0,1} /\ (1 - (1 - 1)) = 1 /\ 1 # (1 - 1)
    OBVIOUS
  <1> QED BY <1>1, <1>2

THEOREM
  ASSUME TypeOK, Inv, Next
  PROVE  TypeOK' /\ Inv'
PROOF
  <1>0. /\ trying \in [{0,1} -> BOOLEAN]
        /\ pc \in [{0,1} -> {"a", "b", "cs", "Done"}]
        /\ \A i \in {0,1} :
              /\ pc[i] \in {"b", "cs"} => trying[i]
              /\ pc[i] = "cs" => pc[1-i] # "cs"
    BY DEF TypeOK, Inv
  <1>1. CASE \E self \in {0,1}: a(self)
    <2>1. PICK self \in {0,1}: a(self)
      BY <1>1
    <2>2. /\ (1 - self) \in {0,1}
          /\ (1 - (1 - self)) = self
          /\ self # (1 - self)
      BY <2>1, L_Sub01
    <2>3. /\ pc[self] = "a"
          /\ trying' = [trying EXCEPT ![self] = TRUE]
          /\ pc' = [pc EXCEPT ![self] = "b"]
      BY <2>1 DEF a
    <2>4. trying' \in [{0,1} -> BOOLEAN]
      BY <2>3, <1>0, <2>1
    <2>5. pc' \in [{0,1} -> {"a", "b", "cs", "Done"}]
      BY <2>3, <1>0, <2>1
    <2>6. /\ pc'[self] = "b"
          /\ trying'[self] = TRUE
      BY <2>3, <2>1, <1>0
    <2>7. /\ pc'[1-self] = pc[1-self]
          /\ trying'[1-self] = trying[1-self]
      BY <2>3, <2>1, <2>2, <1>0
    <2>8. ASSUME NEW i \in {0,1}
          PROVE  /\ pc'[i] \in {"b", "cs"} => trying'[i]
                 /\ pc'[i] = "cs" => pc'[1-i] # "cs"
      <3>1. i = self \/ i = 1-self
        BY <2>8, <2>2
      <3>2. CASE i = self
        <4>1. pc'[i] = "b" /\ trying'[i] = TRUE
          BY <3>2, <2>6
        <4>2. pc'[i] \in {"b", "cs"} => trying'[i]
          BY <4>1
        <4>3. pc'[i] # "cs"
          BY <4>1
        <4>4. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>3
        <4> QED BY <4>2, <4>4
      <3>3. CASE i = 1-self
        <4>1. /\ trying'[i] = trying[i]
              /\ pc'[i] = pc[i]
          BY <3>3, <2>7
        <4>2. 1-i = self
          BY <3>3, <2>2
        <4>3. pc'[1-i] = "b"
          BY <4>2, <2>6
        <4>4. (pc[i] \in {"b","cs"} => trying[i]) /\ (pc[i] = "cs" => pc[1-i] # "cs")
          BY <2>8, <1>0
        <4>5. pc'[i] \in {"b","cs"} => trying'[i]
          BY <4>1, <4>4
        <4>6. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>3
        <4> QED BY <4>5, <4>6
      <3> QED BY <3>1, <3>2, <3>3
    <2>9. Inv'
      BY <2>8 DEF Inv
    <2>10. TypeOK'
      BY <2>4, <2>5 DEF TypeOK
    <2> QED BY <2>9, <2>10
  <1>2. CASE \E self \in {0,1}: b(self)
    <2>1. PICK self \in {0,1}: b(self)
      BY <1>2
    <2>2. /\ (1 - self) \in {0,1}
          /\ (1 - (1 - self)) = self
          /\ self # (1 - self)
      BY <2>1, L_Sub01
    <2>3. /\ pc[self] = "b"
          /\ ~trying[1-self]
          /\ pc' = [pc EXCEPT ![self] = "cs"]
          /\ trying' = trying
      BY <2>1 DEF b
    <2>4. trying' \in [{0,1} -> BOOLEAN]
      BY <2>3, <1>0
    <2>5. pc' \in [{0,1} -> {"a", "b", "cs", "Done"}]
      BY <2>3, <1>0, <2>1
    <2>6. pc'[self] = "cs"
      BY <2>3, <2>1, <1>0
    <2>7. pc'[1-self] = pc[1-self]
      BY <2>3, <2>1, <2>2, <1>0
    <2>8. trying[self] = TRUE
      BY <2>3, <2>1, <1>0
    <2>9. pc[1-self] # "cs"
      <3>1. pc[1-self] \in {"b","cs"} => trying[1-self]
        BY <2>2, <1>0
      <3>2. ~trying[1-self]
        BY <2>3
      <3>3. pc[1-self] \notin {"b","cs"} \/ FALSE
        BY <3>1, <3>2
      <3> QED BY <3>3
    <2>10. ASSUME NEW i \in {0,1}
           PROVE  /\ pc'[i] \in {"b", "cs"} => trying'[i]
                  /\ pc'[i] = "cs" => pc'[1-i] # "cs"
      <3>1. i = self \/ i = 1-self
        BY <2>10, <2>2
      <3>2. CASE i = self
        <4>1. pc'[i] = "cs"
          BY <3>2, <2>6
        <4>2. trying'[i] = trying[self]
          BY <3>2, <2>3
        <4>3. trying'[i] = TRUE
          BY <4>2, <2>8
        <4>4. pc'[i] \in {"b", "cs"} => trying'[i]
          BY <4>3
        <4>5. 1-i = 1-self
          BY <3>2
        <4>6. pc'[1-i] = pc[1-self]
          BY <4>5, <2>7
        <4>7. pc'[1-i] # "cs"
          BY <4>6, <2>9
        <4>8. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>7
        <4> QED BY <4>4, <4>8
      <3>3. CASE i = 1-self
        <4>1. pc'[i] = pc[1-self]
          BY <3>3, <2>7
        <4>2. trying'[i] = trying[i]
          BY <2>3
        <4>3. 1-i = self
          BY <3>3, <2>2
        <4>4. pc'[1-i] = "cs"
          BY <4>3, <2>6
        <4>5. pc'[i] # "cs"
          BY <4>1, <2>9
        <4>6. pc'[i] \in {"b", "cs"} => trying'[i]
          <5>1. CASE pc'[i] = "b"
            <6>1. pc[i] = "b"
              BY <5>1, <4>1, <3>3
            <6>2. trying[i] = TRUE
              BY <6>1, <2>10, <1>0
            <6> QED BY <6>2, <4>2
          <5>2. CASE pc'[i] \notin {"b", "cs"}
            BY <5>2
          <5> QED BY <5>1, <5>2, <4>5
        <4>7. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>5
        <4> QED BY <4>6, <4>7
      <3> QED BY <3>1, <3>2, <3>3
    <2>11. Inv'
      BY <2>10 DEF Inv
    <2>12. TypeOK'
      BY <2>4, <2>5 DEF TypeOK
    <2> QED BY <2>11, <2>12
  <1>3. CASE \E self \in {0,1}: cs(self)
    <2>1. PICK self \in {0,1}: cs(self)
      BY <1>3
    <2>2. /\ (1 - self) \in {0,1}
          /\ (1 - (1 - self)) = self
          /\ self # (1 - self)
      BY <2>1, L_Sub01
    <2>3. /\ pc[self] = "cs"
          /\ pc' = [pc EXCEPT ![self] = "Done"]
          /\ trying' = trying
      BY <2>1 DEF cs
    <2>4. trying' \in [{0,1} -> BOOLEAN]
      BY <2>3, <1>0
    <2>5. pc' \in [{0,1} -> {"a", "b", "cs", "Done"}]
      BY <2>3, <1>0, <2>1
    <2>6. pc'[self] = "Done"
      BY <2>3, <2>1, <1>0
    <2>7. pc'[1-self] = pc[1-self]
      BY <2>3, <2>1, <2>2, <1>0
    <2>8. ASSUME NEW i \in {0,1}
          PROVE  /\ pc'[i] \in {"b", "cs"} => trying'[i]
                 /\ pc'[i] = "cs" => pc'[1-i] # "cs"
      <3>1. i = self \/ i = 1-self
        BY <2>8, <2>2
      <3>2. CASE i = self
        <4>1. pc'[i] = "Done"
          BY <3>2, <2>6
        <4>2. pc'[i] \notin {"b", "cs"}
          BY <4>1
        <4>3. pc'[i] \in {"b", "cs"} => trying'[i]
          BY <4>2
        <4>4. pc'[i] # "cs"
          BY <4>1
        <4>5. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>4
        <4> QED BY <4>3, <4>5
      <3>3. CASE i = 1-self
        <4>1. pc'[i] = pc[1-self]
          BY <3>3, <2>7
        <4>2. trying'[i] = trying[i]
          BY <2>3
        <4>3. 1-i = self
          BY <3>3, <2>2
        <4>4. pc'[1-i] = "Done"
          BY <4>3, <2>6
        <4>5. pc'[1-i] # "cs"
          BY <4>4
        <4>6. pc'[i] = "cs" => pc'[1-i] # "cs"
          BY <4>5
        <4>7. pc'[i] \in {"b", "cs"} => trying'[i]
          <5>1. CASE pc'[i] \in {"b", "cs"}
            <6>1. pc[i] \in {"b", "cs"}
              BY <5>1, <4>1, <3>3
            <6>2. trying[i] = TRUE
              BY <6>1, <2>8, <1>0
            <6> QED BY <6>2, <4>2
          <5>2. CASE pc'[i] \notin {"b", "cs"}
            BY <5>2
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>6, <4>7
      <3> QED BY <3>1, <3>2, <3>3
    <2>9. Inv'
      BY <2>8 DEF Inv
    <2>10. TypeOK'
      BY <2>4, <2>5 DEF TypeOK
    <2> QED BY <2>9, <2>10
  <1>4. CASE (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
    <2>1. trying' = trying /\ pc' = pc
      BY <1>4 DEF vars
    <2>2. TypeOK'
      BY <2>1, <1>0 DEF TypeOK
    <2>3. Inv'
      BY <2>1, <1>0 DEF Inv
    <2> QED BY <2>2, <2>3
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Next, p, ProcSet
----------------------------------------------------------------------

=============================================================================
