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

-----------------------------------------------------------------------------

Labels == {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}

Wait == {"p5", "p6", "cs"}

Active == {"p4", "p5", "p6", "cs"}

Choosing == {"p2", "p3"}

Done == {"cs", "p7"}

TypeOK ==
  /\ DOMAIN num = P
  /\ DOMAIN flag = P
  /\ DOMAIN pc = P
  /\ DOMAIN unread = P
  /\ DOMAIN max = P
  /\ DOMAIN nxt = P
  /\ \A i \in P : num[i] \in Nat
  /\ \A i \in P : flag[i] \in BOOLEAN
  /\ \A i \in P : pc[i] \in Labels
  /\ \A i \in P : unread[i] \in SUBSET P
  /\ \A i \in P : max[i] \in Nat
  /\ \A i \in P : nxt[i] \in P

Control ==
  /\ \A i \in P : pc[i] \in {"p1", "p2"} => num[i] = 0
  /\ \A i \in P : pc[i] \in Choosing => flag[i]
  /\ \A i \in P : pc[i] \in {"p5", "p6", "cs", "p7"} => ~flag[i]
  /\ \A i \in P : pc[i] \in Active => num[i] # 0
  /\ \A i \in P : pc[i] \in Done => unread[i] = {}
  /\ \A i \in P : pc[i] = "p3" => unread[i] = {}

Safe ==
  \A i, j \in P :
    /\ i # j
    /\ pc[i] \in Wait
    /\ pc[j] \in Active
    /\ j \notin unread[i]
    => LL(i, j)

MaxRead ==
  \A i, j \in P :
    /\ i # j
    /\ pc[i] \in Wait
    /\ pc[j] \in Choosing
    /\ j \notin unread[i]
    /\ i \notin unread[j]
    => num[i] =< max[j]

P6Read ==
  \A i, j \in P :
    /\ i # j
    /\ pc[i] = "p6"
    /\ nxt[i] = j
    /\ pc[j] \in Choosing
    /\ i \notin unread[j]
    => num[i] =< max[j]

IndInv == TypeOK /\ Control /\ Safe /\ MaxRead /\ P6Read

LEMMA ExceptApply ==
  ASSUME NEW f, NEW x \in DOMAIN f, NEW y, NEW z \in DOMAIN f
  PROVE  [f EXCEPT ![x] = y][z] = IF z = x THEN y ELSE f[z]
PROOF OBVIOUS

P1Repeat(self) ==
  /\ pc[self] = "p1"
  /\ unread' = [unread EXCEPT ![self] = P \ {self}]
  /\ max' = [max EXCEPT ![self] = 0]
  /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
  /\ pc' = [pc EXCEPT ![self] = "p1"]
  /\ num' = num
  /\ nxt' = nxt

P1Go(self) ==
  /\ pc[self] = "p1"
  /\ unread' = [unread EXCEPT ![self] = P \ {self}]
  /\ max' = [max EXCEPT ![self] = 0]
  /\ flag' = [flag EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "p2"]
  /\ num' = num
  /\ nxt' = nxt

LEMMA InitIndInv == Init => IndInv
PROOF
  BY SMT DEF Init, IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
             Labels, Wait, Active, Choosing, Done, LL, P, ProcSet

LEMMA P1Case == \A self \in P : p1(self) => P1Repeat(self) \/ P1Go(self)
PROOF
  BY SMT DEF p1, P1Repeat, P1Go

LEMMA P1RepeatNum == \A self \in P : P1Repeat(self) => num' = num
PROOF
  BY SMT DEF P1Repeat

LEMMA P1RepeatNxt == \A self \in P : P1Repeat(self) => nxt' = nxt
PROOF
  BY SMT DEF P1Repeat

LEMMA P1RepeatInd == \A self \in P : IndInv /\ P1Repeat(self) => IndInv'
PROOF
  BY P1RepeatNum, P1RepeatNxt, ExceptApply, SMTT(20)
     DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
         Labels, Wait, Active, Choosing, Done, LL, P1Repeat, P

LEMMA P1GoInd == \A self \in P : IndInv /\ P1Go(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, P1Go, P

LEMMA P1Ind == \A self \in P : IndInv /\ p1(self) => IndInv'
PROOF
  BY P1Case, P1RepeatInd, P1GoInd

LEMMA P2Ind == \A self \in P : IndInv /\ p2(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p2, P

LEMMA P3Ind == \A self \in P : IndInv /\ p3(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p3, P

LEMMA P4Ind == \A self \in P : IndInv /\ p4(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p4, P

LEMMA P5Ind == \A self \in P : IndInv /\ p5(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p5, P

LEMMA P6Ind == \A self \in P : IndInv /\ p6(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p6, P

LEMMA CSInd == \A self \in P : IndInv /\ cs(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, cs, P

LEMMA P7Ind == \A self \in P : IndInv /\ p7(self) => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, p7, P

LEMMA PInd == \A self \in P : IndInv /\ p(self) => IndInv'
PROOF
  BY P1Ind, P2Ind, P3Ind, P4Ind, P5Ind, P6Ind, CSInd, P7Ind DEF p

LEMMA StutterInd == IndInv /\ UNCHANGED vars => IndInv'
PROOF
  BY SMTT(10) DEF IndInv, TypeOK, Control, Safe, MaxRead, P6Read,
                Labels, Wait, Active, Choosing, Done, LL, vars

LEMMA NextIndInv == IndInv /\ [Next]_vars => IndInv'
PROOF
  BY PInd, StutterInd DEF Next, vars

LEMMA PNat == \A i \in P : i \in Nat
PROOF
  BY SimpleArithmetic DEF P

LEMMA LLAsym == TypeOK => \A i, j \in P : i # j => ~(LL(i, j) /\ LL(j, i))
PROOF
  BY PNat, SMT, SimpleArithmetic DEF LL, TypeOK

LEMMA CsFacts == /\ "cs" \in Wait /\ "cs" \in Active /\ "cs" \in Done
PROOF
  BY DEF Wait, Active, Done

LEMMA CsUnread == Control => \A i \in P : pc[i] = "cs" => unread[i] = {}
PROOF
  BY CsFacts, SMT DEF Control

LEMMA CsOrder ==
  IndInv => \A i, j \in P :
              /\ i # j
              /\ pc[i] = "cs"
              /\ pc[j] = "cs"
              => LL(i, j)
PROOF
  BY CsFacts, CsUnread, SMT DEF IndInv, Control, Safe

LEMMA IndInvImpliesMutualExclusion == IndInv => MutualExclusion
PROOF
  BY LLAsym, CsOrder, SMT DEF IndInv, MutualExclusion

THEOREM Spec => []MutualExclusion
PROOF
  BY InitIndInv, NextIndInv, IndInvImpliesMutualExclusion, PTL DEF Spec
=============================================================================
