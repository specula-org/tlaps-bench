------------ MODULE AtomicBakery_MutualExclusion ----------------------------

EXTENDS Naturals, TLAPS

CONSTANT N 
ASSUME N \in Nat

P == 1..N 

VARIABLES num, flag, pc

LL(j, i) == \/ num[j] < num[i]
            \/ /\ num[i] = num[j]
               /\ j =< i

VARIABLES unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

ProcSet == (P)

Init == 
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        
        /\ unread \in [P -> SUBSET P]
        /\ max \in [P -> Nat]
        /\ nxt \in [P -> P]
        /\ pc = [self \in ProcSet |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << num, nxt >>

p2(self) == /\ pc[self] = "p2"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
                       /\ UNCHANGED << unread, max >>
            /\ UNCHANGED << num, flag, nxt >>

p3(self) == /\ pc[self] = "p3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, max, nxt >>

p5(self) == /\ pc[self] = "p5"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ LL(self, nxt[self])
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ cs(self) \/ p7(self)

Next == (\E self \in P: p(self))

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

PCSet == {"p1","p2","p3","p4","p5","p6","cs","p7"}

TypeOK == /\ num \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ unread \in [P -> SUBSET P]
          /\ max \in [P -> Nat]
          /\ nxt \in [P -> P]
          /\ pc \in [P -> PCSet]

GG(i,j) == \/ num[i] < num[j]
           \/ /\ num[i] = num[j]
              /\ i < j

Behind(i,j) ==
  /\ num[i] > 0
  /\ \/ pc[j] = "p1"
     \/ /\ pc[j] = "p2"
        /\ i \in unread[j]
     \/ /\ pc[j] \in {"p2","p3"}
        /\ max[j] >= num[i]
     \/ /\ pc[j] \in {"p4","p5","p6","cs","p7"}
        /\ GG(i,j)

NextOK(i) == Behind(i, nxt[i]) \/ (num[nxt[i]] > 0 /\ GG(nxt[i], i))

ProcInv(i) ==
       /\ (pc[i] \in {"p1","p2","p3"}) => (num[i] = 0)
       /\ (pc[i] \in {"p4","p5","p6","cs","p7"}) => (num[i] > 0)
       /\ flag[i] = (pc[i] \in {"p2","p3","p4"})
       /\ (pc[i] # "p1") => (i \notin unread[i])
       /\ (pc[i] = "cs") => (unread[i] = {})
       /\ (pc[i] = "p6") => NextOK(i)
       /\ (pc[i] \in {"p5","p6","cs"}) =>
             (\A j \in P : (j # i /\ j \notin unread[i]) => Behind(i,j))

IInv ==
  /\ TypeOK
  /\ \A i \in P : ProcInv(i)

LEMMA GGFacts ==
  ASSUME NEW i \in P, NEW j \in P, i # j, num[i] \in Nat, num[j] \in Nat
  PROVE  /\ ~(GG(i,j) /\ GG(j,i))
         /\ (GG(i,j) \/ GG(j,i))
PROOF BY DEF GG, P

LEMMA OnlySelf ==
  ASSUME TypeOK, NEW self \in P, p(self), NEW r \in P, r # self
  PROVE  /\ num'[r] = num[r]
         /\ flag'[r] = flag[r]
         /\ pc'[r] = pc[r]
         /\ unread'[r] = unread[r]
         /\ max'[r] = max[r]
         /\ nxt'[r] = nxt[r]
PROOF
<1> USE DEF TypeOK, P
<1>1. CASE p1(self)  BY <1>1 DEF p1
<1>2. CASE p2(self)  BY <1>2 DEF p2
<1>3. CASE p3(self)  BY <1>3 DEF p3
<1>4. CASE p4(self)  BY <1>4 DEF p4
<1>5. CASE p5(self)  BY <1>5 DEF p5
<1>6. CASE p6(self)  BY <1>6 DEF p6
<1>7. CASE cs(self)  BY <1>7 DEF cs
<1>8. CASE p7(self)  BY <1>8 DEF p7
<1>9. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8, p(self) DEF p

LEMMA BehindMono ==
  ASSUME IInv, NEW i \in P, NEW k \in P, i # k, p(k), num[i] > 0, Behind(i,k)
  PROVE  Behind(i,k)'
PROOF
<1> USE DEF P
<1>t. TypeOK  BY DEF IInv
<1>n. num'[i] = num[i]  BY OnlySelf, <1>t
<1>p. num'[i] > 0  BY <1>n
<1> USE <1>t, <1>n, <1>p DEF TypeOK
<1>1. CASE p1(k)
   <2>1. pc'[k] = "p2" /\ unread'[k] = P \ {k}  BY <1>1 DEF p1
   <2>2. i \in unread'[k]  BY <2>1
   <2> QED  BY <1>p, <2>1, <2>2 DEF Behind
<1>2. CASE p2(k)
   <2>1. pc[k] = "p2"  BY <1>2 DEF p2
   <2>2. i \in unread[k] \/ max[k] >= num[i]   BY <2>1 DEF Behind
   <2>3. CASE unread[k] # {}
      <3>0. pc'[k] = "p2"  BY <1>2, <2>3 DEF p2
      <3>1. PICK m \in unread[k] :
                /\ unread'[k] = unread[k] \ {m}
                /\ \/ (num[m] > max[k] /\ max'[k] = num[m])
                   \/ (num[m] =< max[k] /\ max'[k] = max[k])
         BY <1>2, <2>3, <1>t DEF p2, TypeOK
      <3>m. m \in P  BY <3>1, <1>t DEF TypeOK
      <3>2. max'[k] >= num[i] \/ i \in unread'[k]
         <4>1. CASE max[k] >= num[i]
            BY <3>1, <4>1, <1>t, <3>m DEF TypeOK
         <4>2. CASE i \in unread[k]
            <5>1. CASE m = i
               BY <3>1, <5>1, <1>t, <3>m DEF TypeOK
            <5>2. CASE m # i
               BY <3>1, <4>2, <5>2
            <5> QED BY <5>1, <5>2
         <4> QED BY <2>2, <4>1, <4>2
      <3> QED BY <1>p, <3>0, <3>2 DEF Behind
   <2>4. CASE unread[k] = {}
      <3>1. pc'[k] = "p3" /\ max'[k] = max[k]  BY <1>2, <2>4 DEF p2
      <3>2. max[k] >= num[i]  BY <2>2, <2>4
      <3> QED BY <1>p, <3>1, <3>2 DEF Behind
   <2> QED BY <2>3, <2>4
<1>3. CASE p3(k)
   <2>1. pc[k] = "p3"  BY <1>3 DEF p3
   <2>2. max[k] >= num[i]  BY <2>1 DEF Behind
   <2>3. pc'[k] = "p4" /\ num'[k] = max[k] + 1  BY <1>3 DEF p3
   <2>4. num'[k] > num'[i]   BY <2>2, <2>3, <1>n, <1>t DEF TypeOK
   <2>5. GG(i,k)'  BY <2>4 DEF GG
   <2> QED BY <1>p, <2>3, <2>5 DEF Behind
<1>4. CASE p4(k)
   <2>1. pc[k] = "p4"  BY <1>4 DEF p4
   <2>2. GG(i,k)  BY <2>1 DEF Behind
   <2>3. pc'[k] = "p5" /\ num'[k] = num[k]  BY <1>4 DEF p4
   <2>4. GG(i,k)'  BY <2>2, <2>3, <1>n DEF GG
   <2> QED BY <1>p, <2>3, <2>4 DEF Behind
<1>5. CASE p5(k)
   <2>1. pc[k] = "p5"  BY <1>5 DEF p5
   <2>2. GG(i,k)  BY <2>1 DEF Behind
   <2>3. (pc'[k] = "p6" \/ pc'[k] = "cs") /\ num'[k] = num[k]  BY <1>5 DEF p5
   <2>4. GG(i,k)'  BY <2>2, <2>3, <1>n DEF GG
   <2> QED BY <1>p, <2>3, <2>4 DEF Behind
<1>6. CASE p6(k)
   <2>1. pc[k] = "p6"  BY <1>6 DEF p6
   <2>2. GG(i,k)  BY <2>1 DEF Behind
   <2>3. pc'[k] = "p5" /\ num'[k] = num[k]  BY <1>6 DEF p6
   <2>4. GG(i,k)'  BY <2>2, <2>3, <1>n DEF GG
   <2> QED BY <1>p, <2>3, <2>4 DEF Behind
<1>7. CASE cs(k)
   <2>1. pc[k] = "cs"  BY <1>7 DEF cs
   <2>2. GG(i,k)  BY <2>1 DEF Behind
   <2>3. pc'[k] = "p7" /\ num'[k] = num[k]  BY <1>7 DEF cs
   <2>4. GG(i,k)'  BY <2>2, <2>3, <1>n DEF GG
   <2> QED BY <1>p, <2>3, <2>4 DEF Behind
<1>8. CASE p7(k)
   <2>1. pc'[k] = "p1"  BY <1>8 DEF p7
   <2> QED BY <1>p, <2>1 DEF Behind
<1>9. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8, p(k) DEF p

LEMMA C5Mono ==
  ASSUME IInv, NEW i \in P, NEW k \in P, i # k, p(k), num[i] > 0,
         Behind(i,k) \/ (num[k] > 0 /\ GG(k,i))
  PROVE  Behind(i,k)' \/ (num'[k] > 0 /\ GG(k,i)')
PROOF
<1> USE DEF P
<1>t. TypeOK  BY DEF IInv
<1>n. num'[i] = num[i]  BY OnlySelf, <1>t
<1>pk. ProcInv(k)  BY DEF IInv
<1> USE <1>t, <1>n, <1>pk DEF TypeOK
<1>1. CASE Behind(i,k)
   <2>1. Behind(i,k)'  BY BehindMono, <1>1
   <2> QED BY <2>1
<1>2. CASE num[k] > 0 /\ GG(k,i)
   <2>1. num[k] > 0  BY <1>2
   <2>2. GG(k,i)  BY <1>2
   <2>3. pc[k] \in {"p4","p5","p6","cs","p7"}
      BY <2>1, <1>pk, <1>t DEF ProcInv, TypeOK, PCSet
   <2>4. CASE p4(k) \/ p5(k) \/ p6(k) \/ cs(k)
      <3>1. num'[k] = num[k]  BY <2>4 DEF p4, p5, p6, cs
      <3>2. GG(k,i)'  BY <2>2, <3>1, <1>n DEF GG
      <3> QED BY <2>1, <3>1, <3>2
   <2>5. CASE p7(k)
      <3>1. pc'[k] = "p1"  BY <2>5 DEF p7
      <3>2. Behind(i,k)'  BY <1>n, <3>1 DEF Behind
      <3> QED BY <3>2
   <2>6. p4(k) \/ p5(k) \/ p6(k) \/ cs(k) \/ p7(k)
      BY <2>3, p(k) DEF p, p1, p2, p3
   <2> QED BY <2>4, <2>5, <2>6
<1>3. QED BY <1>1, <1>2

LEMMA OtherProc ==
  ASSUME IInv, NEW self \in P, p(self), NEW i \in P, i # self,
         num'[i] = num[i], flag'[i] = flag[i], pc'[i] = pc[i],
         unread'[i] = unread[i], max'[i] = max[i], nxt'[i] = nxt[i]
  PROVE  ProcInv(i)'
PROOF
<1> USE DEF P
<1>t. TypeOK  BY DEF IInv
<1>0. ProcInv(i)  BY DEF IInv
<1>1. (pc'[i] \in {"p1","p2","p3"}) => (num'[i] = 0)  BY <1>0 DEF ProcInv
<1>2. (pc'[i] \in {"p4","p5","p6","cs","p7"}) => (num'[i] > 0)  BY <1>0 DEF ProcInv
<1>3. flag'[i] = (pc'[i] \in {"p2","p3","p4"})  BY <1>0 DEF ProcInv
<1>4. (pc'[i] # "p1") => (i \notin unread'[i])  BY <1>0 DEF ProcInv
<1>5. (pc'[i] = "cs") => (unread'[i] = {})  BY <1>0 DEF ProcInv
<1>6. (pc'[i] = "p6") => NextOK(i)'
   <2>1. SUFFICES ASSUME pc'[i] = "p6" PROVE NextOK(i)'  OBVIOUS
   <2>2. pc[i] = "p6"  BY <2>1
   <2>3. num[i] > 0  BY <2>2, <1>0 DEF ProcInv
   <2>4. Behind(i, nxt[i]) \/ (num[nxt[i]] > 0 /\ GG(nxt[i], i))  BY <2>2, <1>0 DEF ProcInv, NextOK
   <2>5. nxt[i] \in P  BY <1>t DEF TypeOK
   <2>n. nxt'[i] = nxt[i]  OBVIOUS
   <2>6. CASE nxt[i] = self
      <3>1. Behind(i, self)' \/ (num'[self] > 0 /\ GG(self, i)')
         BY C5Mono, <2>3, <2>4, <2>6
      <3> QED BY <3>1, <2>6, <2>n DEF NextOK
   <2>7. CASE nxt[i] # self
      <3>1. num'[nxt[i]] = num[nxt[i]] /\ pc'[nxt[i]] = pc[nxt[i]]
            /\ unread'[nxt[i]] = unread[nxt[i]] /\ max'[nxt[i]] = max[nxt[i]]
         BY OnlySelf, <2>5, <2>7, <1>t
      <3> QED BY <2>4, <2>n, <3>1 DEF NextOK, Behind, GG
   <2> QED BY <2>6, <2>7
<1>7. (pc'[i] \in {"p5","p6","cs"}) =>
         (\A j \in P : (j # i /\ j \notin unread'[i]) => Behind(i,j)')
   <2>1. SUFFICES ASSUME pc'[i] \in {"p5","p6","cs"}, NEW j \in P, j # i, j \notin unread'[i]
                  PROVE Behind(i,j)'
      OBVIOUS
   <2>2. pc[i] \in {"p5","p6","cs"}  BY <2>1
   <2>3. j \notin unread[i]  BY <2>1
   <2>4. num[i] > 0  BY <2>2, <1>0 DEF ProcInv
   <2>ji. j # i  BY <2>1
   <2>5. Behind(i,j)
      <3>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => Behind(i,jj)
         BY <2>2, <1>0 DEF ProcInv
      <3> QED BY <3>1, <2>3, <2>ji
   <2>6. CASE j = self
      <3>1. Behind(i, self)  BY <2>5, <2>6
      <3>2. Behind(i, self)'  BY BehindMono, <2>4, <3>1
      <3> QED BY <3>2, <2>6
   <2>7. CASE j # self
      <3>1. num'[j] = num[j] /\ pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j]
         BY OnlySelf, <2>7, <1>t
      <3>2. Behind(i,j)' = Behind(i,j)  BY <3>1 DEF Behind, GG
      <3> QED BY <2>5, <3>2
   <2> QED BY <2>6, <2>7
<1> QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF ProcInv

LEMMA TypeNext == TypeOK /\ [Next]_vars => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'  OBVIOUS
<1> USE DEF TypeOK, P, ProcSet, PCSet
<1>1. CASE Next
  <2> SUFFICES ASSUME NEW self \in P, p(self) PROVE TypeOK'  BY <1>1 DEF Next
  <2>1. CASE p1(self)  BY <2>1 DEF p1
  <2>2. CASE p2(self)  BY <2>2 DEF p2
  <2>3. CASE p3(self)  BY <2>3 DEF p3
  <2>4. CASE p4(self)  BY <2>4 DEF p4
  <2>5. CASE p5(self)  BY <2>5 DEF p5
  <2>6. CASE p6(self)  BY <2>6 DEF p6
  <2>7. CASE cs(self)  BY <2>7 DEF cs
  <2>8. CASE p7(self)  BY <2>8 DEF p7
  <2>9. QED BY <2>1,<2>2,<2>3,<2>4,<2>5,<2>6,<2>7,<2>8, p(self) DEF p
<1>2. CASE vars' = vars  BY <1>2 DEF vars
<1>3. QED BY <1>1, <1>2

LEMMA InitInv == Init => IInv
PROOF
<1> SUFFICES ASSUME Init PROVE IInv  OBVIOUS
<1>1. TypeOK  BY DEF Init, TypeOK, ProcSet, P, PCSet
<1>2. ASSUME NEW i \in P PROVE ProcInv(i)
   <2>1. pc[i] = "p1" /\ num[i] = 0 /\ flag[i] = FALSE
      BY DEF Init, ProcSet, P
   <2> QED BY <2>1 DEF ProcInv
<1> QED BY <1>1, <1>2 DEF IInv

LEMMA SafetyInv == IInv => MutualExclusion
PROOF
<1> SUFFICES ASSUME IInv, NEW i \in P, NEW j \in P, i # j, pc[i] = "cs", pc[j] = "cs"
             PROVE FALSE
  BY DEF MutualExclusion
<1>t. TypeOK  BY DEF IInv
<1>0. ProcInv(i) /\ ProcInv(j)  BY DEF IInv
<1>1. unread[i] = {} /\ unread[j] = {}  BY <1>0 DEF ProcInv
<1>2. Behind(i,j)
   <2>1. pc[i] \in {"p5","p6","cs"}  BY pc[i] = "cs"
   <2>2. j \notin unread[i]  BY <1>1
   <2> QED BY <1>0, <2>1, <2>2 DEF ProcInv
<1>3. Behind(j,i)
   <2>1. pc[j] \in {"p5","p6","cs"}  BY pc[j] = "cs"
   <2>2. i \notin unread[j]  BY <1>1
   <2> QED BY <1>0, <2>1, <2>2 DEF ProcInv
<1>4. num[i] \in Nat /\ num[j] \in Nat  BY <1>t DEF TypeOK
<1>5. GG(i,j)  BY <1>2 DEF Behind
<1>6. GG(j,i)  BY <1>3 DEF Behind
<1> QED BY <1>5, <1>6, <1>4, GGFacts

LEMMA NextInv == IInv /\ [Next]_vars => IInv'
PROOF
<1> SUFFICES ASSUME IInv, [Next]_vars PROVE IInv'  OBVIOUS
<1>t. TypeOK  BY DEF IInv
<1> USE <1>t DEF TypeOK, P
<1>type. TypeOK'  BY TypeNext, <1>t
<1>proc. ASSUME NEW i \in P PROVE ProcInv(i)'
   <2>1. CASE vars' = vars
      <3>1. num' = num /\ flag' = flag /\ pc' = pc /\ unread' = unread /\ max' = max /\ nxt' = nxt
         BY <2>1 DEF vars
      <3>2. ProcInv(i)  BY DEF IInv
      <3> QED BY <3>1, <3>2 DEF ProcInv, NextOK, Behind, GG
   <2>2. CASE Next
      <3>0. SUFFICES ASSUME NEW self \in P, p(self) PROVE ProcInv(i)'  BY <2>2 DEF Next
      <3>A. CASE i # self
         <4>1. num'[i] = num[i] /\ flag'[i] = flag[i] /\ pc'[i] = pc[i]
               /\ unread'[i] = unread[i] /\ max'[i] = max[i] /\ nxt'[i] = nxt[i]
            BY OnlySelf, <3>0, <3>A, <1>t
         <4> QED BY OtherProc, <4>1, <3>0, <3>A
      <3>B. CASE i = self
         <4>0. ProcInv(i)  BY DEF IInv
         <4>1. CASE p1(self)
            <5>1. pc[i] = "p1" /\ num'[i] = num[i] /\ flag'[i] = TRUE
                  /\ unread'[i] = P \ {i} /\ pc'[i] = "p2"
               BY <4>1, <3>B DEF p1
            <5>2. num[i] = 0  BY <5>1, <4>0 DEF ProcInv
            <5> QED BY <5>1, <5>2 DEF ProcInv
         <4>2. CASE p2(self)
            <5>1. pc[i] = "p2" /\ num'[i] = num[i] /\ flag'[i] = flag[i]
               BY <4>2, <3>B DEF p2
            <5>2. num[i] = 0  BY <5>1, <4>0 DEF ProcInv
            <5>3. flag[i] = TRUE  BY <5>1, <4>0 DEF ProcInv
            <5>4. i \notin unread[i]  BY <5>1, <4>0 DEF ProcInv
            <5>5. pc'[i] = "p2" \/ pc'[i] = "p3"  BY <4>2, <3>B DEF p2
            <5>6. i \notin unread'[i]  BY <4>2, <3>B, <5>4 DEF p2
            <5> QED BY <5>1, <5>2, <5>3, <5>5, <5>6 DEF ProcInv
         <4>3. CASE p3(self)
            <5>1. pc[i] = "p3" /\ num'[i] = max[i] + 1 /\ pc'[i] = "p4"
                  /\ flag'[i] = flag[i] /\ unread'[i] = unread[i]
               BY <4>3, <3>B DEF p3
            <5>2. flag[i] = TRUE  BY <5>1, <4>0 DEF ProcInv
            <5>3. i \notin unread[i]  BY <5>1, <4>0 DEF ProcInv
            <5>4. max[i] \in Nat  BY DEF TypeOK
            <5>5. num'[i] > 0  BY <5>1, <5>4
            <5> QED BY <5>1, <5>2, <5>3, <5>5 DEF ProcInv
         <4>4. CASE p4(self)
            <5>1. pc[i] = "p4" /\ flag'[i] = FALSE /\ unread'[i] = P \ {i}
                  /\ pc'[i] = "p5" /\ num'[i] = num[i]
               BY <4>4, <3>B DEF p4
            <5>2. num[i] > 0  BY <5>1, <4>0 DEF ProcInv
            <5>3. (pc'[i] \in {"p5","p6","cs"}) =>
                     (\A j \in P : (j # i /\ j \notin unread'[i]) => Behind(i,j)')
               <6>1. SUFFICES ASSUME pc'[i] \in {"p5","p6","cs"}, NEW j \in P, j # i,
                                     j \notin unread'[i]
                              PROVE Behind(i,j)'
                  OBVIOUS
               <6>2. j \in unread'[i]  BY <6>1, <5>1
               <6> QED BY <6>1, <6>2
            <5> QED BY <5>1, <5>2, <5>3 DEF ProcInv
         <4>5. CASE p5(self)
            <5>1. pc[i] = "p5" /\ num'[i] = num[i] /\ flag'[i] = flag[i] /\ unread'[i] = unread[i]
               BY <4>5, <3>B DEF p5
            <5>2. num[i] > 0  BY <5>1, <4>0 DEF ProcInv
            <5>3. flag[i] = FALSE  BY <5>1, <4>0 DEF ProcInv
            <5>4. i \notin unread[i]  BY <5>1, <4>0 DEF ProcInv
            <5>5. CASE unread[i] # {}
               <6>1. PICK m \in unread[i] : nxt'[i] = m /\ ~flag[m] /\ pc'[i] = "p6"
                  BY <4>5, <5>5, <3>B DEF p5
               <6>m. m \in P  BY <6>1 DEF TypeOK
               <6>mi. m # i  BY <6>1, <5>4
               <6>ms. m # self  BY <6>mi, <3>B
               <6>flag. pc[m] \in {"p1","p5","p6","cs","p7"}
                  BY <6>1, <6>m DEF IInv, ProcInv, TypeOK, PCSet
               <6>only. num'[m] = num[m] /\ pc'[m] = pc[m]
                        /\ unread'[m] = unread[m] /\ max'[m] = max[m]
                  BY OnlySelf, <3>0, <6>m, <6>ms, <1>t
               <6>q6. NextOK(i)'
                  <7>1. CASE pc[m] = "p1"
                     <8>1. Behind(i,m)'  BY <5>1, <6>only, <7>1, <5>2 DEF Behind
                     <8> QED BY <8>1, <6>1 DEF NextOK, Behind, GG
                  <7>2. CASE pc[m] \in {"p5","p6","cs","p7"}
                     <8>0. num[m] > 0  BY <6>m, <7>2 DEF IInv, ProcInv
                     <8>1. GG(i,m) \/ GG(m,i)  BY GGFacts, <6>mi, <6>m DEF TypeOK
                     <8>2. CASE GG(i,m)
                        <9>1. Behind(i,m)'  BY <5>1, <6>only, <7>2, <5>2, <8>2 DEF Behind, GG
                        <9> QED BY <9>1, <6>1 DEF NextOK, Behind, GG
                     <8>3. CASE GG(m,i)
                        <9>1. num'[m] > 0 /\ GG(m,i)'  BY <6>only, <8>0, <8>3, <5>1 DEF GG
                        <9> QED BY <9>1, <6>1 DEF NextOK, Behind, GG
                     <8> QED BY <8>1, <8>2, <8>3
                  <7> QED BY <6>flag, <7>1, <7>2
               <6>q7. (pc'[i] \in {"p5","p6","cs"}) =>
                        (\A j \in P : (j # i /\ j \notin unread'[i]) => Behind(i,j)')
                  <7>1. SUFFICES ASSUME NEW j \in P, j # i, j \notin unread'[i]
                                 PROVE Behind(i,j)'
                     BY <6>1
                  <7>2. j \notin unread[i]  BY <7>1, <5>1
                  <7>3. \A jj \in P : (jj # i /\ jj \notin unread[i]) => Behind(i,jj)
                     BY <5>1, <4>0 DEF ProcInv
                  <7>ji. j # i  BY <7>1
                  <7>4. Behind(i,j)  BY <7>3, <7>2, <7>ji
                  <7>js. j # self  BY <7>ji, <3>B
                  <7>5. num'[j] = num[j] /\ pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j]
                     BY OnlySelf, <3>0, <7>1, <7>js, <1>t
                  <7>6. Behind(i,j)' = Behind(i,j)  BY <7>5, <5>1 DEF Behind, GG
                  <7> QED BY <7>4, <7>6
               <6> QED BY <5>1, <5>2, <5>3, <5>4, <6>1, <6>q6, <6>q7 DEF ProcInv
            <5>6. CASE unread[i] = {}
               <6>1. pc'[i] = "cs" /\ unread'[i] = unread[i]
                  BY <4>5, <5>6, <3>B DEF p5
               <6>2. unread'[i] = {}  BY <6>1, <5>6
               <6>q7. \A j \in P : (j # i /\ j \notin unread'[i]) => Behind(i,j)'
                  <7>1. SUFFICES ASSUME NEW j \in P, j # i, j \notin unread'[i]
                                 PROVE Behind(i,j)'
                     OBVIOUS
                  <7>2. j \notin unread[i]  BY <5>6
                  <7>3. \A jj \in P : (jj # i /\ jj \notin unread[i]) => Behind(i,jj)
                     BY <5>1, <4>0 DEF ProcInv
                  <7>ji. j # i  BY <7>1
                  <7>4. Behind(i,j)  BY <7>3, <7>2, <7>ji
                  <7>js. j # self  BY <7>ji, <3>B
                  <7>5. num'[j] = num[j] /\ pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j]
                     BY OnlySelf, <3>0, <7>1, <7>js, <1>t
                  <7>6. Behind(i,j)' = Behind(i,j)  BY <7>5, <5>1 DEF Behind, GG
                  <7> QED BY <7>4, <7>6
               <6> QED BY <5>1, <5>2, <5>3, <6>1, <6>2, <6>q7 DEF ProcInv
            <5> QED BY <5>5, <5>6
         <4>6. CASE p6(self)
            <5>1. pc[i] = "p6" /\ pc'[i] = "p5" /\ num'[i] = num[i] /\ flag'[i] = flag[i]
                  /\ unread'[i] = unread[i] \ {nxt[i]} /\ nxt'[i] = nxt[i]
               BY <4>6, <3>B DEF p6
            <5>2. num[i] > 0  BY <5>1, <4>0 DEF ProcInv
            <5>3. flag[i] = FALSE  BY <5>1, <4>0 DEF ProcInv
            <5>4. i \notin unread[i]  BY <5>1, <4>0 DEF ProcInv
            <5>g. num[nxt[i]] = 0 \/ LL(i, nxt[i])  BY <4>6, <3>B DEF p6
            <5>q7. (pc'[i] \in {"p5","p6","cs"}) =>
                     (\A j \in P : (j # i /\ j \notin unread'[i]) => Behind(i,j)')
               <6>1. SUFFICES ASSUME NEW j \in P, j # i, j \notin unread'[i]
                              PROVE Behind(i,j)'
                  BY <5>1
               <6>ji. j # i  BY <6>1
               <6>2. j \notin unread[i] \/ j = nxt[i]  BY <5>1, <6>1
               <6>3. CASE j \notin unread[i]
                  <7>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => Behind(i,jj)
                     BY <5>1, <4>0 DEF ProcInv
                  <7>2. Behind(i,j)  BY <7>1, <6>3, <6>ji
                  <7>js. j # self  BY <6>ji, <3>B
                  <7>3. num'[j] = num[j] /\ pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j]
                     BY OnlySelf, <3>0, <6>1, <7>js, <1>t
                  <7>4. Behind(i,j)' = Behind(i,j)  BY <7>3, <5>1 DEF Behind, GG
                  <7> QED BY <7>2, <7>4
               <6>4. CASE j = nxt[i]
                  <7>0. nxt[i] \in P  BY DEF TypeOK
                  <7>1. nxt[i] # i  BY <6>ji, <6>4
                  <7>js. j # self  BY <6>1, <3>B
                  <7>2. NextOK(i)  BY <5>1, <4>0 DEF ProcInv
                  <7>3. Behind(i,nxt[i]) \/ (num[nxt[i]] > 0 /\ GG(nxt[i],i))  BY <7>2 DEF NextOK
                  <7>4. num'[j] = num[j] /\ pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j]
                     BY OnlySelf, <3>0, <6>1, <7>js, <1>t
                  <7>5. Behind(i,j)' = Behind(i,j)  BY <7>4, <5>1 DEF Behind, GG
                  <7>6. ~(GG(i,nxt[i]) /\ GG(nxt[i],i))  BY GGFacts, <7>0, <7>1 DEF TypeOK
                  <7>7. Behind(i,nxt[i])
                     <8>1. CASE Behind(i,nxt[i])  BY <8>1
                     <8>2. CASE num[nxt[i]] > 0 /\ GG(nxt[i],i)
                        <9>1. LL(i, nxt[i])  BY <5>g, <8>2
                        <9>2. GG(i, nxt[i])  BY <9>1, <7>1, <7>0 DEF LL, GG
                        <9> QED BY <9>2, <8>2, <7>6
                     <8> QED BY <7>3, <8>1, <8>2
                  <7>8. Behind(i,j)  BY <7>7, <6>4
                  <7> QED BY <7>5, <7>8
               <6> QED BY <6>2, <6>3, <6>4
            <5> QED BY <5>1, <5>2, <5>3, <5>4, <5>q7 DEF ProcInv
         <4>7. CASE cs(self)
            <5>1. pc[i] = "cs" /\ pc'[i] = "p7" /\ num'[i] = num[i]
                  /\ flag'[i] = flag[i] /\ unread'[i] = unread[i]
               BY <4>7, <3>B DEF cs
            <5>2. num[i] > 0  BY <5>1, <4>0 DEF ProcInv
            <5>3. flag[i] = FALSE  BY <5>1, <4>0 DEF ProcInv
            <5>4. i \notin unread[i]  BY <5>1, <4>0 DEF ProcInv
            <5> QED BY <5>1, <5>2, <5>3, <5>4 DEF ProcInv
         <4>8. CASE p7(self)
            <5>1. pc[i] = "p7" /\ num'[i] = 0 /\ pc'[i] = "p1" /\ flag'[i] = flag[i]
               BY <4>8, <3>B DEF p7
            <5>2. flag[i] = FALSE  BY <5>1, <4>0 DEF ProcInv
            <5> QED BY <5>1, <5>2 DEF ProcInv
         <4>9. QED BY <4>1,<4>2,<4>3,<4>4,<4>5,<4>6,<4>7,<4>8, <3>0 DEF p
      <3> QED BY <3>A, <3>B
   <2> QED BY <2>1, <2>2 DEF Next
<1> QED BY <1>type, <1>proc DEF IInv

THEOREM Spec => []MutualExclusion
PROOF
<1>1. Init => IInv  BY InitInv
<1>2. IInv /\ [Next]_vars => IInv'  BY NextInv
<1>3. IInv => MutualExclusion  BY SafetyInv
<1>4. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================

