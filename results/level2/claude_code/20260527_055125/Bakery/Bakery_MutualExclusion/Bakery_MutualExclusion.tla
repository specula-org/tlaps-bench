----------------------------- MODULE Bakery_MutualExclusion ---------------------------------

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
            /\ \E repeat \in BOOLEAN:
                 IF repeat
                    THEN /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                         /\ pc' = [pc EXCEPT ![self] = "p1"]
                    ELSE /\ flag' = [flag EXCEPT ![self] = TRUE]
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
            /\ \E repeat \in BOOLEAN:
                 \E k \in Nat:
                   IF repeat
                      THEN /\ num' = [num EXCEPT ![self] = k]
                           /\ pc' = [pc EXCEPT ![self] = "p3"]
                      ELSE /\ \E i \in {j \in Nat : j > max[self]}:
                                num' = [num EXCEPT ![self] = i]
                           /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ \E repeat \in BOOLEAN:
                 IF repeat
                    THEN /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                         /\ pc' = [pc EXCEPT ![self] = "p4"]
                    ELSE /\ flag' = [flag EXCEPT ![self] = FALSE]
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
            /\ \E repeat \in BOOLEAN:
                 \E k \in Nat:
                   IF repeat
                      THEN /\ num' = [num EXCEPT ![self] = k]
                           /\ pc' = [pc EXCEPT ![self] = "p7"]
                      ELSE /\ num' = [num EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ cs(self) \/ p7(self)

Next == (\E self \in P: p(self))

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                               /\ pc[j] = "cs"
-----------------------------------------------------------------------------

PCBar == {"p1","p2","p3","p4","p5","p6","cs","p7"}

TypeOK == /\ num \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ pc \in [P -> PCBar]
          /\ unread \in [P -> SUBSET P]
          /\ max \in [P -> Nat]
          /\ nxt \in [P -> P]

After(i, j) ==
  /\ num[i] > 0
  /\ \/ (pc[j] \in {"p1","p7"})
     \/ ((pc[j] = "p2") /\ ((i \in unread[j]) \/ (max[j] >= num[i])))
     \/ ((pc[j] = "p3") /\ (max[j] >= num[i]))
     \/ ((pc[j] \in {"p4","p5","p6","cs"}) /\ (LL(i, j))
            /\ ((pc[j] \in {"p5","p6"}) => (i \in unread[j])))

HH(i, j) ==
  /\ num[i] > 0
  /\ \/ (pc[j] \in {"p1","p7"})
     \/ ((pc[j] = "p2") /\ ((i \in unread[j]) \/ (max[j] >= num[i])))
     \/ ((pc[j] = "p3") /\ (max[j] >= num[i]))
     \/ (pc[j] \in {"p4","p5","p6","cs"})

IInv ==
  /\ TypeOK
  /\ \A i \in P : (pc[i] \in {"p2","p3"}) => flag[i]
  /\ \A i \in P : (pc[i] \in {"p4","p5","p6","cs"}) => (num[i] > 0)
  /\ \A i \in P : (pc[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread[i]) => After(i, j)
  /\ \A i \in P : (pc[i] = "p6") => HH(i, nxt[i])
  /\ \A i \in P : (pc[i] \in {"p5","p6","cs"}) => (i \notin unread[i])
  /\ \A i \in P : (pc[i] = "p6") => (nxt[i] \in unread[i])
  /\ \A i \in P : (pc[i] = "cs") => (unread[i] = {})

LEMMA NatP == \A i \in P : i \in Nat
  BY DEF P

LEMMA InitInv == Init => IInv
<1> SUFFICES ASSUME Init PROVE IInv  OBVIOUS
<1> USE DEF Init, ProcSet, P
<1>1. TypeOK  BY DEF TypeOK, PCBar
<1>2. \A i \in P : pc[i] = "p1"  OBVIOUS
<1> QED  BY <1>1, <1>2 DEF IInv

LEMMA InvImpliesME == IInv => MutualExclusion
<1> SUFFICES ASSUME IInv, NEW i \in P, NEW j \in P, i # j,
                    pc[i] = "cs", pc[j] = "cs"
             PROVE  FALSE
  BY DEF MutualExclusion
<1> USE NatP
<1>1. unread[i] = {} /\ unread[j] = {}  BY DEF IInv
<1>2. After(i, j)
  <2>1. j \in P \ {i}  BY <1>1
  <2>2. j \notin unread[i]  BY <1>1
  <2> QED  BY <2>1, <2>2 DEF IInv
<1>3. After(j, i)
  <2>1. i \in P \ {j}  BY <1>1
  <2>2. i \notin unread[j]  BY <1>1
  <2> QED  BY <2>1, <2>2 DEF IInv
<1>4. LL(i, j) /\ LL(j, i)  BY <1>2, <1>3 DEF After
<1>5. num[i] \in Nat /\ num[j] \in Nat  BY DEF IInv, TypeOK
<1> QED  BY <1>4, <1>5, NatP DEF LL

LEMMA StutterNext == ASSUME IInv, vars' = vars PROVE IInv'
<1>0. /\ num' = num /\ flag' = flag /\ pc' = pc
      /\ unread' = unread /\ max' = max /\ nxt' = nxt
  BY DEF vars
<1> QED  BY <1>0 DEF IInv, TypeOK, After, HH, LL

LEMMA CSNext == ASSUME IInv, NEW self \in P, cs(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ flag' = flag /\ unread' = unread
      /\ max' = max /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![self] = "p7"]
      /\ pc[self] = "cs"
  BY DEF cs
<1>p. \A i \in P : pc'[i] = IF i = self THEN "p7" ELSE pc[i]
  BY <1>0 DEF IInv, TypeOK
<1>t. TypeOK'  BY <1>0 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>p DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)  BY <1>0, <1>p DEF IInv
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>1. i # self  BY <1>0, <1>p
  <2>2. pc[i] \in {"p5","p6","cs"} /\ num'[i] = num[i] /\ unread'[i] = unread[i]
    BY <1>0, <1>p, <2>1 DEF TypeOK
  <2>3. After(i,j)  BY <2>2, <1>0 DEF IInv
  <2>4. num[i] > 0  BY <2>3 DEF After
  <2>5. CASE j = self
    <3>1. pc'[j] = "p7"  BY <1>p, <2>5
    <3> QED  BY <2>2, <2>4, <3>1 DEF After
  <2>6. CASE j # self
    <3>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>p, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF After, LL
  <2> QED  BY <2>5, <2>6
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>0, <1>p
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>p, <2>1 DEF TypeOK
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. pc'[nxt[i]] = "p7"  BY <1>p, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>p, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])  BY <1>0, <1>p DEF IInv
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])  BY <1>0, <1>p DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})  BY <1>0, <1>p DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P7Next == ASSUME IInv, NEW self \in P, p7(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ flag' = flag /\ unread' = unread /\ max' = max /\ nxt' = nxt
      /\ pc[self] = "p7"
  BY DEF p7
<1>1. /\ num' \in [P -> Nat]
      /\ pc' \in [P -> PCBar]
      /\ \A i \in P : (i # self) => (num'[i] = num[i] /\ pc'[i] = pc[i])
      /\ pc'[self] \in {"p1","p7"}
  BY DEF p7, IInv, TypeOK, PCBar
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>1 DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)  BY <1>0, <1>1 DEF IInv
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ num'[i] = num[i] /\ unread'[i] = unread[i]
    BY <1>0, <1>1, <2>1 DEF TypeOK
  <2>3. After(i,j)  BY <2>2, <1>0 DEF IInv
  <2>4. num[i] > 0  BY <2>3 DEF After
  <2>5. CASE j = self
    <3>1. pc'[j] \in {"p1","p7"}  BY <1>1, <2>5
    <3> QED  BY <2>2, <2>4, <3>1 DEF After
  <2>6. CASE j # self
    <3>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>1, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF After, LL
  <2> QED  BY <2>5, <2>6
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1 DEF TypeOK
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. pc'[nxt[i]] \in {"p1","p7"}  BY <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])  BY <1>0, <1>1 DEF IInv
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])  BY <1>0, <1>1 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})  BY <1>0, <1>1 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P1Next == ASSUME IInv, NEW self \in P, p1(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ nxt' = nxt /\ pc[self] = "p1"
      /\ unread' = [unread EXCEPT ![self] = P \ {self}]
      /\ max' = [max EXCEPT ![self] = 0]
  BY DEF p1
<1>1. /\ flag' \in [P -> BOOLEAN] /\ pc' \in [P -> PCBar]
      /\ pc'[self] \in {"p1","p2"}
      /\ (pc'[self] = "p2") => flag'[self]
      /\ \A k \in P : (k # self) => (flag'[k] = flag[k] /\ pc'[k] = pc[k])
  BY DEF p1, IInv, TypeOK, PCBar
<1>u. /\ unread'[self] = P \ {self}
      /\ \A k \in P : (k # self) => (unread'[k] = unread[k] /\ max'[k] = max[k])
  BY <1>0 DEF IInv, TypeOK
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>1 DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)  BY <1>0, <1>1 DEF IInv
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ num'[i] = num[i] /\ unread'[i] = unread[i]
    BY <1>0, <1>1, <1>u, <2>1 DEF TypeOK
  <2>3. After(i,j)  BY <2>2, <1>0 DEF IInv
  <2>4. num[i] > 0  BY <2>3 DEF After
  <2>5. CASE j = self
    <3>1. i \in unread'[self]  BY <1>u, <2>1
    <3>2. pc'[j] \in {"p1","p2"}  BY <1>1, <2>5
    <3> QED  BY <2>2, <2>4, <3>1, <3>2, <2>5 DEF After
  <2>6. CASE j # self
    <3>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>1, <1>u, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF After, LL
  <2> QED  BY <2>5, <2>6
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1 DEF TypeOK
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. i \in unread'[self]  BY <1>u, <2>1
    <3>2. pc'[nxt[i]] \in {"p1","p2"}  BY <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1, <3>2, <2>5 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <1>u, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"} PROVE i \notin unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>1, <1>u, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE nxt'[i] \in unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ unread'[i] = unread[i] /\ nxt'[i] = nxt[i]  BY <1>0, <1>1, <1>u, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "cs" PROVE unread'[i] = {}
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "cs" /\ unread'[i] = unread[i]  BY <1>1, <1>u, <2>1
  <2> QED  BY <2>2 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P4Next == ASSUME IInv, NEW self \in P, p4(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ max' = max /\ nxt' = nxt /\ pc[self] = "p4"
      /\ unread' = [unread EXCEPT ![self] = P \ {self}]
  BY DEF p4
<1>1. /\ flag' \in [P -> BOOLEAN] /\ pc' \in [P -> PCBar]
      /\ pc'[self] \in {"p4","p5"}
      /\ \A k \in P : (k # self) => (flag'[k] = flag[k] /\ pc'[k] = pc[k])
  BY DEF p4, IInv, TypeOK, PCBar
<1>u. /\ unread'[self] = P \ {self}
      /\ \A k \in P : (k # self) => (unread'[k] = unread[k])
  BY <1>0 DEF IInv, TypeOK
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>1 DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p4","p5","p6","cs"} PROVE num'[i] > 0
    OBVIOUS
  <2>0. CASE i = self  BY <1>0, <2>0 DEF IInv
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p4","p5","p6","cs"} /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>0. CASE i = self
    <3>1. unread'[i] = P \ {self}  BY <1>u, <2>0
    <3> QED  BY <3>1, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>1, <1>u, <2>1
    <3>2. After(i,j)  BY <3>1, <2>1 DEF IInv
    <3>3. num[i] > 0 /\ num'[i] = num[i]  BY <3>2, <1>0 DEF After
    <3>4. CASE j = self
      <4>1. i \in unread'[self]  BY <1>u, <2>1
      <4>2. pc'[j] \in {"p4","p5"}  BY <1>1, <3>4
      <4>3. LL(i, j)  BY <3>2, <3>4, <1>0 DEF After
      <4> QED  BY <3>3, <4>1, <4>2, <4>3, <3>4, <1>0 DEF After, LL
    <3>5. CASE j # self
      <4>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
        BY <1>0, <1>1, <1>u, <3>5
      <4> QED  BY <3>2, <3>3, <4>1, <1>0 DEF After, LL
    <3> QED  BY <3>4, <3>5
  <2> QED  BY <2>0, <2>1
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1 DEF TypeOK
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. pc'[nxt[i]] \in {"p4","p5"}  BY <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <1>u, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"} PROVE i \notin unread'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. unread'[i] = P \ {self}  BY <1>u, <2>0
    <3> QED  BY <3>1, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>1, <1>u, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE nxt'[i] \in unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ unread'[i] = unread[i] /\ nxt'[i] = nxt[i]  BY <1>0, <1>1, <1>u, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "cs" PROVE unread'[i] = {}
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "cs" /\ unread'[i] = unread[i]  BY <1>1, <1>u, <2>1
  <2> QED  BY <2>2 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P2Next == ASSUME IInv, NEW self \in P, p2(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ flag' = flag /\ nxt' = nxt /\ pc[self] = "p2"
  BY DEF p2
<1>1. /\ pc' \in [P -> PCBar] /\ unread' \in [P -> SUBSET P] /\ max' \in [P -> Nat]
      /\ pc'[self] \in {"p2","p3"}
      /\ \A k \in P : (k # self) =>
            (unread'[k] = unread[k] /\ max'[k] = max[k] /\ pc'[k] = pc[k])
  BY DEF p2, IInv, TypeOK, PCBar
<1>m. /\ max'[self] >= max[self]
      /\ \A k \in P : (k \in unread[self] /\ k \notin unread'[self]) => max'[self] >= num[k]
      /\ (pc'[self] = "p3") => (unread[self] = {} /\ max'[self] = max[self])
      /\ max'[self] \in Nat /\ max[self] \in Nat
  BY DEF p2, IInv, TypeOK
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p2","p3"} PROVE flag'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. flag'[i] = flag[i] /\ pc[i] = "p2"  BY <1>0, <2>0
    <3> QED  BY <3>1 DEF IInv
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p2","p3"} /\ flag'[i] = flag[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p4","p5","p6","cs"} PROVE num'[i] > 0
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p4","p5","p6","cs"} /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>1, <2>1
  <2>3. After(i,j)  BY <2>2, <2>1 DEF IInv
  <2>4. num[i] > 0 /\ num'[i] = num[i] /\ num[i] \in Nat
    BY <2>3, <1>0 DEF After, IInv, TypeOK
  <2>5. CASE j = self
    <3>1. i \in unread[self] \/ max[self] >= num[i]  BY <2>3, <2>5, <1>0 DEF After
    <3>2. pc'[j] \in {"p2","p3"}  BY <1>1, <2>5
    <3> QED  BY <2>4, <3>1, <3>2, <1>m, <2>5 DEF After
  <2>6. CASE j # self
    <3>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>1, <2>6
    <3> QED  BY <2>3, <2>4, <3>1, <1>0 DEF After, LL
  <2> QED  BY <2>5, <2>6
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P /\ num[i] \in Nat  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. i \in unread[self] \/ max[self] >= num[i]  BY <2>3, <2>5, <1>0 DEF HH
    <3>2. pc'[nxt[i]] \in {"p2","p3"}  BY <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1, <3>2, <1>m, <2>5 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"} PROVE i \notin unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE nxt'[i] \in unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ unread'[i] = unread[i] /\ nxt'[i] = nxt[i]  BY <1>0, <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "cs" PROVE unread'[i] = {}
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "cs" /\ unread'[i] = unread[i]  BY <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P3Next == ASSUME IInv, NEW self \in P, p3(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ flag' = flag /\ unread' = unread /\ max' = max /\ nxt' = nxt /\ pc[self] = "p3"
  BY DEF p3
<1>1. /\ num' \in [P -> Nat] /\ pc' \in [P -> PCBar]
      /\ pc'[self] \in {"p3","p4"}
      /\ (pc'[self] = "p4") => (num'[self] > max[self])
      /\ \A k \in P : (k # self) => (num'[k] = num[k] /\ pc'[k] = pc[k])
  BY DEF p3, IInv, TypeOK, PCBar
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p2","p3"} PROVE flag'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. flag'[i] = flag[i] /\ pc[i] = "p3"  BY <1>0, <2>0
    <3> QED  BY <3>1 DEF IInv
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p2","p3"} /\ flag'[i] = flag[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p4","p5","p6","cs"} PROVE num'[i] > 0
    OBVIOUS
  <2>0. CASE i = self
    <3>1. pc'[i] = "p4" /\ num'[i] > max[i]  BY <1>1, <2>0
    <3>2. max[i] \in Nat /\ num'[i] \in Nat  BY <1>1 DEF IInv, TypeOK
    <3> QED  BY <3>1, <3>2
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p4","p5","p6","cs"} /\ num'[i] = num[i]  BY <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
  <2>3. After(i,j)  BY <2>2, <1>0 DEF IInv
  <2>4. num[i] > 0 /\ num'[i] = num[i] /\ num[i] \in Nat
    BY <2>3, <1>1, <2>1 DEF After, IInv, TypeOK
  <2>5. CASE j = self
    <3>1. max[self] >= num[i]  BY <2>3, <2>5, <1>0 DEF After
    <3>2. max[self] \in Nat /\ num'[self] \in Nat  BY <1>1 DEF IInv, TypeOK
    <3>3. pc'[j] \in {"p3","p4"} /\ max'[j] = max[j]  BY <1>0, <1>1, <2>5
    <3> QED  BY <2>4, <3>1, <3>2, <3>3, <1>1, <2>5 DEF After, LL
  <2>6. CASE j # self
    <3>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>1, <2>6
    <3> QED  BY <2>3, <2>4, <3>1, <1>0 DEF After, LL
  <2> QED  BY <2>5, <2>6
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. max[self] >= num[i]  BY <2>3, <2>5, <1>0 DEF HH
    <3>2. pc'[nxt[i]] \in {"p3","p4"} /\ max'[nxt[i]] = max[nxt[i]]  BY <1>0, <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1, <3>2, <2>5 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])  BY <1>0, <1>1 DEF IInv
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])  BY <1>0, <1>1 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})  BY <1>0, <1>1 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P5Next == ASSUME IInv, NEW self \in P, p5(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ flag' = flag /\ unread' = unread /\ max' = max /\ pc[self] = "p5"
  BY DEF p5
<1>1. /\ pc' \in [P -> PCBar] /\ nxt' \in [P -> P]
      /\ pc'[self] \in {"p6","cs"}
      /\ \A k \in P : (k # self) => (pc'[k] = pc[k] /\ nxt'[k] = nxt[k])
  BY DEF p5, IInv, TypeOK, PCBar
<1>th. /\ (pc'[self] = "p6") => (nxt'[self] \in unread[self] /\ ~ flag[nxt'[self]])
       /\ (pc'[self] = "cs") => (unread[self] = {})
  BY DEF p5, IInv, TypeOK
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>1 DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p4","p5","p6","cs"} PROVE num'[i] > 0
    OBVIOUS
  <2>0. CASE i = self
    <3>1. pc[self] = "p5" /\ num'[i] = num[i]  BY <1>0, <2>0
    <3> QED  BY <3>1, <2>0 DEF IInv
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p4","p5","p6","cs"} /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>0. CASE i = self
    <3>1. pc[i] = "p5" /\ unread'[i] = unread[i] /\ num'[i] = num[i]  BY <1>0, <2>0
    <3>2. After(i,j)  BY <3>1, <2>0 DEF IInv
    <3>3. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
      BY <1>0, <1>1, <2>0
    <3> QED  BY <3>2, <3>1, <3>3, <1>0 DEF After, LL
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i] /\ num'[i] = num[i]
      BY <1>0, <1>1, <2>1
    <3>2. After(i,j)  BY <3>1, <2>1 DEF IInv
    <3>3. num[i] > 0  BY <3>2 DEF After
    <3>4. CASE j = self
      <4>1. LL(i, j) /\ i \in unread[self]  BY <3>2, <3>4, <1>0 DEF After
      <4>2. pc'[j] \in {"p6","cs"}  BY <1>1, <3>4
      <4> QED  BY <3>1, <3>3, <4>1, <4>2, <1>0, <3>4 DEF After, LL
    <3>5. CASE j # self
      <4>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
        BY <1>0, <1>1, <3>5
      <4> QED  BY <3>2, <3>1, <3>3, <4>1, <1>0 DEF After, LL
    <3> QED  BY <3>4, <3>5
  <2> QED  BY <2>0, <2>1
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>0. CASE i = self
    <3>1. nxt'[i] \in unread[self] /\ ~ flag[nxt'[i]]  BY <1>th, <2>0
    <3>2. num'[i] = num[i] /\ num[i] > 0  BY <1>0, <2>0 DEF IInv
    <3>3. nxt'[i] # self /\ nxt'[i] \in P  BY <3>1, <2>0, <1>0, <1>1 DEF IInv, TypeOK
    <3>4. pc'[nxt'[i]] = pc[nxt'[i]] /\ flag'[nxt'[i]] = flag[nxt'[i]]  BY <1>0, <1>1, <3>3
    <3>5. pc[nxt'[i]] \notin {"p2","p3"} /\ pc[nxt'[i]] \in PCBar
      BY <3>1, <3>4, <3>3 DEF IInv, TypeOK
    <3> QED  BY <3>2, <3>4, <3>5 DEF HH, PCBar
  <2>1. CASE i # self
    <3>1. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
    <3>2. HH(i, nxt[i])  BY <3>1 DEF IInv
    <3>3. num[i] > 0 /\ nxt[i] \in P  BY <3>2 DEF HH, IInv, TypeOK
    <3>4. CASE nxt[i] = self
      <4>1. pc'[nxt[i]] \in {"p6","cs"}  BY <1>1, <3>3, <3>4
      <4> QED  BY <3>1, <3>3, <4>1, <3>4 DEF HH
    <3>5. CASE nxt[i] # self
      <4>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
            /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
        BY <1>0, <1>1, <3>3, <3>5
      <4> QED  BY <3>2, <3>1, <4>1 DEF HH
    <3> QED  BY <3>1, <3>4, <3>5
  <2> QED  BY <2>0, <2>1
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"} PROVE i \notin unread'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. pc[self] = "p5" /\ unread'[i] = unread[i]  BY <1>0, <2>0
    <3> QED  BY <3>1, <2>0 DEF IInv
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE nxt'[i] \in unread'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. nxt'[i] \in unread[self]  BY <1>th, <2>0
    <3> QED  BY <3>1, <1>0, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "cs" PROVE unread'[i] = {}
    OBVIOUS
  <2>0. CASE i = self
    <3>1. unread[self] = {}  BY <1>th, <2>0
    <3> QED  BY <3>1, <1>0, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] = "cs" /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA P6Next == ASSUME IInv, NEW self \in P, p6(self) PROVE IInv'
<1> USE DEF P, ProcSet
<1>0. /\ num' = num /\ flag' = flag /\ max' = max /\ nxt' = nxt /\ pc[self] = "p6"
      /\ (num[nxt[self]] = 0 \/ LL(self, nxt[self]))
      /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
      /\ pc' = [pc EXCEPT ![self] = "p5"]
  BY DEF p6
<1>1. /\ pc' \in [P -> PCBar] /\ unread' \in [P -> SUBSET P]
      /\ pc'[self] = "p5"
      /\ unread'[self] = unread[self] \ {nxt[self]}
      /\ \A k \in P : (k # self) => (pc'[k] = pc[k] /\ unread'[k] = unread[k])
  BY <1>0 DEF IInv, TypeOK, PCBar
<1>n. /\ nxt[self] \in unread[self] /\ self \notin unread[self]
      /\ nxt[self] # self /\ nxt[self] \in P
      /\ num[self] > 0 /\ self \in Nat /\ num[self] \in Nat
  BY <1>0, NatP DEF IInv, TypeOK
<1>t. TypeOK'  BY <1>0, <1>1 DEF IInv, TypeOK, PCBar
<1>2. \A i \in P : (pc'[i] \in {"p2","p3"}) => flag'[i]  BY <1>0, <1>1 DEF IInv
<1>3. \A i \in P : (pc'[i] \in {"p4","p5","p6","cs"}) => (num'[i] > 0)
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p4","p5","p6","cs"} PROVE num'[i] > 0
    OBVIOUS
  <2>0. CASE i = self  BY <1>0, <1>n, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p4","p5","p6","cs"} /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>4. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) =>
        \A j \in P \ {i} : (j \notin unread'[i]) => After(i, j)'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"},
                      NEW j \in P \ {i}, j \notin unread'[i]
               PROVE  After(i,j)'
    OBVIOUS
  <2>0. CASE i = self
    <3>1. num'[i] = num[i] /\ num[i] > 0 /\ unread'[i] = unread[self] \ {nxt[self]}
      BY <1>0, <1>1, <1>n, <2>0
    <3>2. CASE j \notin unread[self]
      <4>1. After(i, j)  BY <3>2, <1>0, <2>0 DEF IInv
      <4>2. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
        BY <1>0, <1>1, <2>0
      <4> QED  BY <4>1, <3>1, <4>2, <1>0 DEF After, LL
    <3>3. CASE j \in unread[self]
      <4>0. j = nxt[self]  BY <3>1, <3>3
      <4>1. HH(self, nxt[self])  BY <1>0 DEF IInv
      <4>2. j # self /\ j \in P /\ j \in Nat /\ num[j] \in Nat  BY <4>0, <1>n, NatP DEF IInv, TypeOK
      <4>3. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
        BY <1>0, <1>1, <4>2
      <4>4. num[j] = 0 \/ LL(self, j)  BY <1>0, <4>0
      <4>5. CASE pc[j] \in {"p4","p5","p6","cs"}
        <5>1. LL(self, j)  BY <4>4, <4>5, <4>2 DEF IInv
        <5>2. (pc[j] \in {"p5","p6"}) => (self \in unread[j])
          <6> SUFFICES ASSUME pc[j] \in {"p5","p6"}, self \notin unread[j] PROVE FALSE
            OBVIOUS
          <6>1. After(j, self)  BY <4>2, <2>0 DEF IInv
          <6>2. LL(j, self)  BY <6>1, <1>0 DEF After
          <6> QED  BY <5>1, <6>2, <4>2, <1>n DEF LL
        <5> QED  BY <3>1, <4>0, <4>2, <4>3, <4>5, <5>1, <5>2, <1>0, <2>0 DEF After, LL
      <4>6. CASE pc[j] \notin {"p4","p5","p6","cs"}
        <5> QED  BY <4>1, <3>1, <4>3, <4>6, <4>0, <2>0 DEF After, HH
      <4> QED  BY <4>5, <4>6
    <3> QED  BY <3>2, <3>3
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i] /\ num'[i] = num[i]
      BY <1>0, <1>1, <2>1
    <3>2. After(i,j)  BY <3>1, <2>1 DEF IInv
    <3>3. num[i] > 0 /\ i \in Nat /\ num[i] \in Nat  BY <3>2, <2>1, NatP DEF After, IInv, TypeOK
    <3>4. CASE j = self
      <4>1. LL(i, self) /\ i \in unread[self]  BY <3>2, <3>4, <1>0 DEF After
      <4>2. i # nxt[self]
        <5> SUFFICES ASSUME i = nxt[self] PROVE FALSE  OBVIOUS
        <5>1. LL(self, i)  BY <1>0, <3>3
        <5> QED  BY <5>1, <4>1, <3>3, <1>n DEF LL
      <4>3. i \in unread'[self]  BY <4>1, <4>2, <1>1, <2>1
      <4>4. pc'[j] = "p5"  BY <1>1, <3>4
      <4> QED  BY <3>1, <3>3, <4>1, <4>3, <4>4, <1>0, <3>4 DEF After, LL
    <3>5. CASE j # self
      <4>1. pc'[j] = pc[j] /\ unread'[j] = unread[j] /\ max'[j] = max[j] /\ num'[j] = num[j]
        BY <1>0, <1>1, <3>5
      <4> QED  BY <3>2, <3>1, <3>3, <4>1, <1>0 DEF After, LL
    <3> QED  BY <3>4, <3>5
  <2> QED  BY <2>0, <2>1
<1>5. \A i \in P : (pc'[i] = "p6") => HH(i, nxt[i])'
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE HH(i, nxt[i])'
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ num'[i] = num[i]  BY <1>0, <1>1, <2>1
  <2>3. HH(i, nxt[i])  BY <2>2 DEF IInv
  <2>4. num[i] > 0 /\ nxt[i] \in P  BY <2>3 DEF HH, IInv, TypeOK
  <2>5. CASE nxt[i] = self
    <3>1. pc'[nxt[i]] = "p5"  BY <1>1, <2>4, <2>5
    <3> QED  BY <2>2, <2>4, <3>1, <2>5 DEF HH
  <2>6. CASE nxt[i] # self
    <3>1. pc'[nxt[i]] = pc[nxt[i]] /\ unread'[nxt[i]] = unread[nxt[i]]
          /\ max'[nxt[i]] = max[nxt[i]] /\ num'[nxt[i]] = num[nxt[i]]
      BY <1>0, <1>1, <2>4, <2>6
    <3> QED  BY <2>3, <2>2, <3>1 DEF HH
  <2> QED  BY <2>2, <2>5, <2>6
<1>6. \A i \in P : (pc'[i] \in {"p5","p6","cs"}) => (i \notin unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] \in {"p5","p6","cs"} PROVE i \notin unread'[i]
    OBVIOUS
  <2>0. CASE i = self
    <3>1. unread'[i] = unread[self] \ {nxt[self]} /\ self \notin unread[self]  BY <1>1, <1>n, <2>0
    <3> QED  BY <3>1, <2>0
  <2>1. CASE i # self
    <3>1. pc[i] \in {"p5","p6","cs"} /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
    <3> QED  BY <3>1 DEF IInv
  <2> QED  BY <2>0, <2>1
<1>7. \A i \in P : (pc'[i] = "p6") => (nxt'[i] \in unread'[i])
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "p6" PROVE nxt'[i] \in unread'[i]
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "p6" /\ nxt'[i] = nxt[i] /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1>8. \A i \in P : (pc'[i] = "cs") => (unread'[i] = {})
  <2> SUFFICES ASSUME NEW i \in P, pc'[i] = "cs" PROVE unread'[i] = {}
    OBVIOUS
  <2>1. i # self  BY <1>1
  <2>2. pc[i] = "cs" /\ unread'[i] = unread[i]  BY <1>0, <1>1, <2>1
  <2> QED  BY <2>2 DEF IInv
<1> QED  BY <1>t,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8 DEF IInv

LEMMA InvNext == IInv /\ [Next]_vars => IInv'
<1> SUFFICES ASSUME IInv, [Next]_vars PROVE IInv'  OBVIOUS
<1>1. CASE Next
  <2> SUFFICES ASSUME NEW self \in P, p(self) PROVE IInv'  BY <1>1 DEF Next
  <2>1. CASE p1(self)  BY <2>1, P1Next
  <2>2. CASE p2(self)  BY <2>2, P2Next
  <2>3. CASE p3(self)  BY <2>3, P3Next
  <2>4. CASE p4(self)  BY <2>4, P4Next
  <2>5. CASE p5(self)  BY <2>5, P5Next
  <2>6. CASE p6(self)  BY <2>6, P6Next
  <2>7. CASE cs(self)  BY <2>7, CSNext
  <2>8. CASE p7(self)  BY <2>8, P7Next
  <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF p
<1>2. CASE vars' = vars  BY <1>2, StutterNext
<1> QED  BY <1>1, <1>2 DEF Next

THEOREM Spec => []MutualExclusion
<1>1. Init => IInv  BY InitInv
<1>2. IInv /\ [Next]_vars => IInv'  BY InvNext
<1>3. IInv => MutualExclusion  BY InvImpliesME
<1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
