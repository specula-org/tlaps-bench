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

Labels == {"p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"}

Doorway == {"p2", "p3", "p4"}

PreTicket == {"p1", "p2", "p3"}

HasTicket == {"p4", "p5", "p6", "p7", "p8"}

Waiting == {"p5", "p6", "p7", "p8"}

PriorityOK(self, other) ==
  \/ num[other] = 0
  \/ IF self > other THEN num[other] > num[self]
                     ELSE num[other] >= num[self]

Relevant(self, other) ==
  \/ self \notin unread[other]
  \/ /\ pc[other] = "p6"
     /\ nxt[other] = self

ProcNext == \E self \in P : p(self)

TypeOK ==
  /\ num \in [P -> Nat]
  /\ flag \in [P -> BOOLEAN]
  /\ pc \in [P -> Labels]
  /\ unread \in [P -> SUBSET P]
  /\ max \in [P -> Nat]
  /\ nxt \in [P -> P]

IndInv ==
  /\ TypeOK
  /\ \A i \in P : flag[i] = (pc[i] \in Doorway)
  /\ \A i \in P : pc[i] \in PreTicket => num[i] = 0
  /\ \A i \in P : pc[i] \in HasTicket => num[i] > 0
  /\ \A i \in P : pc[i] \in {"p2", "p5", "p6"} => i \notin unread[i]
  /\ \A i \in P : pc[i] \in {"p3", "p7", "p8"} => unread[i] = {}
  /\ \A i \in P : pc[i] = "p6" => nxt[i] \in unread[i]
  /\ \A i,j \in P : /\ pc[i] \in {"p2", "p3"}
                    /\ j \notin unread[i]
                    /\ pc[j] \in Waiting
                    /\ Relevant(i,j)
                    => num[j] <= max[i]
  /\ \A i,j \in P : /\ pc[i] \in Waiting
                    /\ j \notin unread[i]
                    => PriorityOK(i,j)

-----------------------------------------------------------------------------

LEMMA InitIndInv == Init => IndInv
PROOF BY SMTT(30) DEF Init, IndInv, TypeOK, Labels, Doorway, PreTicket,
                     HasTicket, Waiting, PriorityOK, Relevant, PsubsetNat

LEMMA P1IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p1(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p1, vars, PsubsetNat

LEMMA P2IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p2(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p2, vars, PsubsetNat

LEMMA P3IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p3(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p3, vars, PsubsetNat

LEMMA P4IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p4(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p4, vars, PsubsetNat

LEMMA P5IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p5(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p5, vars, PsubsetNat

LEMMA P6IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p6(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p6, vars, PsubsetNat

LEMMA P7IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p7(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p7, vars, PsubsetNat

LEMMA P8IndInv == ASSUME NEW self \in P
                  PROVE  IndInv /\ p8(self) => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, p8, vars, PsubsetNat

LEMMA ProcIndInv == IndInv /\ ProcNext => IndInv'
PROOF BY P1IndInv, P2IndInv, P3IndInv, P4IndInv, P5IndInv, P6IndInv,
         P7IndInv, P8IndInv DEF ProcNext, p

LEMMA StutterIndInv == IndInv /\ UNCHANGED vars => IndInv'
PROOF BY SMTT(30) DEF IndInv, TypeOK, Labels, Doorway, PreTicket, HasTicket,
                     Waiting, PriorityOK, Relevant, vars

LEMMA StepIndInv == IndInv /\ [Next]_vars => IndInv'
PROOF BY ProcIndInv, StutterIndInv DEF Next, ProcNext, vars

LEMMA PriorityContradiction ==
  ASSUME NEW i \in P, NEW j \in P,
         i # j,
         num \in [P -> Nat],
         num[i] > 0,
         num[j] > 0,
         PriorityOK(i,j),
         PriorityOK(j,i)
  PROVE  FALSE
PROOF BY PsubsetNat, SMTT(30) DEF PriorityOK

LEMMA IndInvMutualExclusion == IndInv => MutualExclusion
PROOF BY PriorityContradiction, Zenon DEF IndInv, TypeOK, Labels, Doorway,
                                      PreTicket, HasTicket, Waiting,
                                      PriorityOK, Relevant, MutualExclusion

-----------------------------------------------------------------------------

THEOREM Safety == Spec => [] MutualExclusion
PROOF
<1>1. Spec => []IndInv
  BY InitIndInv, StepIndInv, PTL DEF Spec
<1>2. Spec => []IndInv
  BY <1>1
<1>3. []IndInv => []MutualExclusion
  BY IndInvMutualExclusion, PTL
<1>4. QED
  BY <1>2, <1>3

=============================================================================
