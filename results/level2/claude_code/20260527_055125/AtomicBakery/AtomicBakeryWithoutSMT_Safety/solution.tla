------------ MODULE AtomicBakeryWithoutSMT_Safety ----------------------------

EXTENDS Naturals, TLAPS

CONSTANT P
ASSUME PsubsetNat == P \subseteq Nat

CONSTANT defaultInitValue
VARIABLES num, flag, pc, unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

Init == 
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        
        /\ unread \in [P -> SUBSET P]
        /\ max \in [P -> Nat]
        /\ nxt \in [P -> P]
        /\ pc = [self \in P |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << num, nxt >>

p2(self) == /\ pc[self] = "p2"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            /\ unread' = [unread EXCEPT
                                            ![self] = unread[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT
                                                    ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED max
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
                            nxt' = [nxt EXCEPT
                                      ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p7"]
                       /\ UNCHANGED nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ IF self > nxt[self] THEN num[nxt[self]] > num[self]
                                      ELSE num[nxt[self]] >= num[self]
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p8(self) == /\ pc[self] = "p8"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
              \/ p6(self) \/ p7(self) \/ p8(self)

Next == (\E self \in P: p(self))
           \/ 
              ((\A self \in P: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i,j \in P : (i # j) => ~ /\ pc[i] = "p7"
                                               /\ pc[j] = "p7"

-----------------------------------------------------------------------------

PCSet == {"p1","p2","p3","p4","p5","p6","p7","p8"}

TypeOK ==
  /\ num \in [P -> Nat]
  /\ flag \in [P -> BOOLEAN]
  /\ unread \in [P -> SUBSET P]
  /\ max \in [P -> Nat]
  /\ nxt \in [P -> P]
  /\ pc \in [P -> PCSet]

Before(i, j) == \/ num[i] < num[j]
                \/ (num[i] = num[j] /\ i < j)

WillFallBehind(i, j) ==
  \/ pc[j] = "p1"
  \/ (pc[j] = "p2" /\ i \in unread[j])
  \/ (pc[j] = "p2" /\ i \notin unread[j] /\ num[i] =< max[j])
  \/ (pc[j] = "p3" /\ num[i] =< max[j])

IInv ==
  /\ TypeOK
  /\ \A i \in P :
       /\ (pc[i] \in {"p2","p3","p4"}) => flag[i]
       /\ (pc[i] \in {"p1","p2","p3"}) => num[i] = 0
       /\ (pc[i] \in {"p4","p5","p6","p7","p8"}) => num[i] > 0
       /\ (pc[i] \in {"p5","p6","p7","p8"}) => i \notin unread[i]
       /\ pc[i] = "p7" => unread[i] = {}
       /\ pc[i] = "p6" => nxt[i] \in unread[i]
       /\ pc[i] = "p6" => (num[nxt[i]] > 0 \/ WillFallBehind(i, nxt[i]))
       /\ (pc[i] \in {"p5","p6","p7","p8"}) =>
             \A j \in P : (j # i /\ j \notin unread[i]) =>
                            (Before(i, j) \/ WillFallBehind(i, j))

-----------------------------------------------------------------------------

LEMMA InitInv == Init => IInv
  <1> SUFFICES ASSUME Init PROVE IInv  OBVIOUS
  <1> USE DEF Init
  <1>1. TypeOK  BY DEF TypeOK, PCSet
  <1>2. ASSUME NEW i \in P
        PROVE  /\ (pc[i] \in {"p2","p3","p4"}) => flag[i]
               /\ (pc[i] \in {"p1","p2","p3"}) => num[i] = 0
               /\ (pc[i] \in {"p4","p5","p6","p7","p8"}) => num[i] > 0
               /\ (pc[i] \in {"p5","p6","p7","p8"}) => i \notin unread[i]
               /\ pc[i] = "p7" => unread[i] = {}
               /\ pc[i] = "p6" => nxt[i] \in unread[i]
               /\ pc[i] = "p6" => (num[nxt[i]] > 0 \/ WillFallBehind(i, nxt[i]))
               /\ (pc[i] \in {"p5","p6","p7","p8"}) =>
                     \A j \in P : (j # i /\ j \notin unread[i]) =>
                                    (Before(i, j) \/ WillFallBehind(i, j))
    BY DEF TypeOK
  <1>3. QED  BY <1>1, <1>2 DEF IInv

-----------------------------------------------------------------------------

LEMMA InvImpliesME == IInv => MutualExclusion
  <1> SUFFICES ASSUME IInv,
                      NEW i \in P, NEW j \in P, i # j,
                      pc[i] = "p7", pc[j] = "p7"
               PROVE  FALSE
    BY DEF MutualExclusion
  <1> USE PsubsetNat DEF IInv, TypeOK
  <1>1. unread[i] = {} /\ unread[j] = {}  BY DEF IInv
  <1>2. Before(i, j)  BY <1>1 DEF WillFallBehind
  <1>3. Before(j, i)  BY <1>1 DEF WillFallBehind
  <1>4. QED  BY <1>2, <1>3 DEF Before

-----------------------------------------------------------------------------

Inv7(i) == /\ (pc[i] \in {"p2","p3","p4"}) => flag[i]
           /\ (pc[i] \in {"p1","p2","p3"}) => num[i] = 0
           /\ (pc[i] \in {"p4","p5","p6","p7","p8"}) => num[i] > 0
           /\ (pc[i] \in {"p5","p6","p7","p8"}) => i \notin unread[i]
           /\ pc[i] = "p7" => unread[i] = {}
           /\ pc[i] = "p6" => nxt[i] \in unread[i]
           /\ pc[i] = "p6" => (num[nxt[i]] > 0 \/ WillFallBehind(i, nxt[i]))

CL17(i) == /\ (pc'[i] \in {"p2","p3","p4"}) => flag'[i]
           /\ (pc'[i] \in {"p1","p2","p3"}) => num'[i] = 0
           /\ (pc'[i] \in {"p4","p5","p6","p7","p8"}) => num'[i] > 0
           /\ (pc'[i] \in {"p5","p6","p7","p8"}) => i \notin unread'[i]
           /\ pc'[i] = "p7" => unread'[i] = {}
           /\ pc'[i] = "p6" => nxt'[i] \in unread'[i]
           /\ pc'[i] = "p6" => (num'[nxt'[i]] > 0 \/ WillFallBehind(i, nxt[i])')

PassedClause(i, j) ==
  (pc'[i] \in {"p5","p6","p7","p8"} /\ j # i /\ j \notin unread'[i])
       => (Before(i, j)' \/ WillFallBehind(i, j)')

LEMMA NextInv == IInv /\ [Next]_vars => IInv'
  <1> SUFFICES ASSUME IInv, [Next]_vars PROVE IInv'  OBVIOUS
  <1> USE PsubsetNat
  <1>0. TypeOK  BY DEF IInv
  <1> USE <1>0
  <1>1. CASE \E self \in P : p(self)
    <2> SUFFICES ASSUME NEW self \in P, p(self) PROVE IInv'  BY <1>1
    <2>1. CASE p1(self)
      <3>0. /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ num' = num /\ nxt' = nxt
        BY <2>1 DEF p1
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>0, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>2. CASE p2(self)
      <3>T. TypeOK'  BY <2>2, SMT DEF p2, TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <2>2, SMT DEF CL17, p2, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <2>2, SMT DEF Before, WillFallBehind, TypeOK, p2
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <2>2, SMT DEF TypeOK, PCSet, p2
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>3. CASE p3(self)
      <3>0. /\ pc[self] = "p3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ flag' = flag /\ unread' = unread /\ max' = max /\ nxt' = nxt
        BY <2>3 DEF p3
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>1b. Before(i, j) \/ WillFallBehind(i, j)  BY <4>1, <5>1
          <5>1c. num[i] = num'[i] /\ num[self] = 0  BY <3>0, SMT DEF TypeOK, IInv
          <5>2. QED  BY <5>1b, <5>1c, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>0, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>4. CASE p4(self)
      <3>0. /\ pc[self] = "p4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unread' = [unread EXCEPT ![self] = P \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ num' = num /\ max' = max /\ nxt' = nxt
        BY <2>4 DEF p4
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>0, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>5. CASE p5(self)
      <3>g. /\ pc[self] = "p5" /\ num' = num /\ flag' = flag /\ unread' = unread /\ max' = max
        BY <2>5 DEF p5
      <3>pc. pc' = [pc EXCEPT ![self] = "p6"] \/ pc' = [pc EXCEPT ![self] = "p7"]
        BY <2>5, SMT DEF p5
      <3>T. TypeOK'  BY <2>5, SMT DEF p5, TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        <4>Hi. Inv7(i)  BY DEF IInv, Inv7
        <4>Hs. Inv7(self)  BY DEF IInv, Inv7
        <4>1. CASE unread[self] = {}
          <5>0. nxt' = nxt /\ pc' = [pc EXCEPT ![self] = "p7"]  BY <2>5, <4>1, SMT DEF p5
          <5>c1. (pc'[i] \in {"p2","p3","p4"}) => flag'[i]  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c2. (pc'[i] \in {"p1","p2","p3"}) => num'[i] = 0  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c3. (pc'[i] \in {"p4","p5","p6","p7","p8"}) => num'[i] > 0  BY <3>g, <5>0, <4>Hi, <4>Hs, SMT DEF Inv7, TypeOK, PCSet
          <5>c4. (pc'[i] \in {"p5","p6","p7","p8"}) => i \notin unread'[i]  BY <3>g, <5>0, <4>1, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c5. pc'[i] = "p7" => unread'[i] = {}  BY <3>g, <5>0, <4>1, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c6. pc'[i] = "p6" => nxt'[i] \in unread'[i]  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c7. pc'[i] = "p6" => (num'[nxt'[i]] > 0 \/ WillFallBehind(i, nxt[i])')  BY <3>g, <5>0, <4>Hi, <4>Hs, SMT DEF Inv7, WillFallBehind, TypeOK, PCSet
          <5>Q. QED  BY <5>c1, <5>c2, <5>c3, <5>c4, <5>c5, <5>c6, <5>c7 DEF CL17
        <4>2. CASE unread[self] # {}
          <5>0. /\ (\E k \in unread[self] : nxt' = [nxt EXCEPT ![self] = k])
                /\ ~ flag[nxt'[self]] /\ pc' = [pc EXCEPT ![self] = "p6"]
            BY <2>5, <4>2, SMT DEF p5
          <5>b. PICK k \in unread[self] : nxt' = [nxt EXCEPT ![self] = k]  BY <5>0
          <5>c. nxt'[self] = k /\ ~ flag[k] /\ k \in unread[self] /\ k \in P /\ k # self
            BY <5>0, <5>b, <3>g, <4>Hs, SMT DEF Inv7, TypeOK
          <5>Hk. Inv7(k)  BY <5>c DEF IInv, Inv7
          <5>c1. (pc'[i] \in {"p2","p3","p4"}) => flag'[i]  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c2. (pc'[i] \in {"p1","p2","p3"}) => num'[i] = 0  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c3. (pc'[i] \in {"p4","p5","p6","p7","p8"}) => num'[i] > 0  BY <3>g, <5>0, <4>Hi, <4>Hs, SMT DEF Inv7, TypeOK, PCSet
          <5>c4. (pc'[i] \in {"p5","p6","p7","p8"}) => i \notin unread'[i]  BY <3>g, <5>0, <4>Hi, <4>Hs, SMT DEF Inv7, TypeOK, PCSet
          <5>c5. pc'[i] = "p7" => unread'[i] = {}  BY <3>g, <5>0, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c6. pc'[i] = "p6" => nxt'[i] \in unread'[i]  BY <3>g, <5>0, <5>b, <5>c, <4>Hi, SMT DEF Inv7, TypeOK, PCSet
          <5>c7. pc'[i] = "p6" => (num'[nxt'[i]] > 0 \/ WillFallBehind(i, nxt[i])')  BY <3>g, <5>0, <5>b, <5>c, <5>Hk, <4>Hi, <4>Hs, SMT DEF Inv7, WillFallBehind, TypeOK, PCSet
          <5>Q. QED  BY <5>c1, <5>c2, <5>c3, <5>c4, <5>c5, <5>c6, <5>c7 DEF CL17
        <4>3. QED  BY <4>1, <4>2, <3>g DEF p5
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>g, <3>pc, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>g, <3>pc, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>6. CASE p6(self)
      <3>0. /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ IF self > nxt[self] THEN num[nxt[self]] > num[self]
                                      ELSE num[nxt[self]] >= num[self]
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ num' = num /\ flag' = flag /\ max' = max /\ nxt' = nxt
        BY <2>6 DEF p6
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. i = self /\ j = nxt[self] /\ pc[self] = "p6"  BY <4>2, <3>0, SMT DEF TypeOK
          <5>2. num[nxt[self]] > 0 \/ WillFallBehind(self, nxt[self])  BY <3>0 DEF IInv
          <5>3. QED  BY <5>1, <5>2, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>7. CASE p7(self)
      <3>0. /\ pc[self] = "p7"
            /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ num' = num /\ flag' = flag /\ unread' = unread /\ max' = max /\ nxt' = nxt
        BY <2>7 DEF p7
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>0, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>8. CASE p8(self)
      <3>0. /\ pc[self] = "p8"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ flag' = flag /\ unread' = unread /\ max' = max /\ nxt' = nxt
        BY <2>8 DEF p8
      <3>T. TypeOK'  BY <3>0 DEF TypeOK, PCSet
      <3>C. ASSUME NEW i \in P PROVE CL17(i)
        BY <3>0, SMT DEF CL17, IInv, TypeOK, WillFallBehind, PCSet
      <3>D. ASSUME NEW i \in P, NEW j \in P PROVE PassedClause(i, j)
        <4> SUFFICES ASSUME pc'[i] \in {"p5","p6","p7","p8"}, j # i, j \notin unread'[i]
                     PROVE Before(i, j)' \/ WillFallBehind(i, j)'  BY DEF PassedClause
        <4>1. CASE pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i]
          <5>1. \A jj \in P : (jj # i /\ jj \notin unread[i]) => (Before(i, jj) \/ WillFallBehind(i, jj))  BY <4>1 DEF IInv
          <5>2. QED  BY <4>1, <5>1, <3>0, SMT DEF Before, WillFallBehind, TypeOK
        <4>2. CASE ~(pc[i] \in {"p5","p6","p7","p8"} /\ j \notin unread[i])
          <5>1. FALSE  BY <4>2, <3>0, SMT DEF TypeOK, PCSet
          <5>2. QED  BY <5>1
        <4>3. QED  BY <4>1, <4>2
      <3>Z. QED  BY <3>T, <3>C, <3>D DEF IInv, CL17, PassedClause
    <2>9. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF p
  <1>2. CASE UNCHANGED vars
    <2>1. /\ num' = num /\ flag' = flag /\ pc' = pc
          /\ unread' = unread /\ max' = max /\ nxt' = nxt
      BY <1>2 DEF vars
    <2>2. QED  BY <2>1 DEF IInv, TypeOK, Before, WillFallBehind
  <1>3. QED  BY <1>1, <1>2 DEF Next

-----------------------------------------------------------------------------

THEOREM Safety == Spec => [] MutualExclusion
<1>1. Init => IInv  BY InitInv
<1>2. IInv /\ [Next]_vars => IInv'  BY NextInv
<1>3. IInv => MutualExclusion  BY InvImpliesME
<1>4. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
