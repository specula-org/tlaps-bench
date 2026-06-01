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

PCVals == {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}
Choosing == {"p2", "p3", "p4"}
Early == {"p1", "p2", "p3"}
Numbered == {"p4", "p5", "p6", "cs", "p7"}
Waiting == {"p5", "p6", "cs", "p7"}

TypeOK ==
        /\ num \in [P -> Nat]
        /\ flag \in [P -> BOOLEAN]
        /\ pc \in [P -> PCVals]
        /\ unread \in [P -> SUBSET P]
        /\ max \in [P -> Nat]
        /\ nxt \in [P -> P]

FlagOK == \A i \in P : flag[i] = (pc[i] \in Choosing)

NumOK == \A i \in P :
            /\ pc[i] \in Early => num[i] = 0
            /\ pc[i] \in Numbered => num[i] > 0

UnreadOK == \A i \in P :
              /\ pc[i] # "p1" => unread[i] \subseteq P \ {i}
              /\ pc[i] \in {"p3", "p4"} => unread[i] = {}
              /\ pc[i] \in {"cs", "p7"} => unread[i] = {}
              /\ pc[i] = "p6" => nxt[i] \in unread[i]

Passed(i, j) == flag[j] \/ num[j] = 0 \/ LL(i, j)

PassedOK == \A i,j \in P :
              /\ i # j
              /\ pc[i] \in Waiting
              /\ j \notin unread[i]
              => Passed(i, j)

DoorOK == \A i,j \in P :
            /\ i # j
            /\ pc[j] = "p4"
            /\ pc[i] \in Waiting
            /\ j \notin unread[i]
            => LL(i, j)

MaxOK == \A i,j \in P :
           /\ i # j
           /\ pc[i] \in {"p2", "p3"}
           /\ j \notin unread[i]
           /\ pc[j] \in Waiting
           /\ \/ i \notin unread[j]
              \/ /\ pc[j] = "p6"
                 /\ nxt[j] = i
           => num[j] =< max[i]

IndInv ==
        /\ TypeOK
        /\ FlagOK
        /\ NumOK
        /\ UnreadOK
        /\ PassedOK
        /\ DoorOK
        /\ MaxOK

LEMMA ExceptHit == \A S, T, f, x, v :
  /\ f \in [S -> T]
  /\ x \in S
  => [f EXCEPT ![x] = v][x] = v
PROOF OBVIOUS

LEMMA ExceptOther == \A S, T, f, x, v, y :
  /\ f \in [S -> T]
  /\ x \in S
  /\ y \in S
  /\ y # x
  => [f EXCEPT ![x] = v][y] = f[y]
PROOF OBVIOUS

LEMMA ExceptFunction == \A S, T, f, x, v :
  /\ f \in [S -> T]
  /\ x \in S
  /\ v \in T
  => [f EXCEPT ![x] = v] \in [S -> T]
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther

LEMMA SetMinusIntro == \A S, x, y :
  /\ y \in S
  /\ y # x
  => y \in S \ {x}
PROOF BY SMT

LEMMA SetMinusSelf == \A S, x : x \notin S \ {x}
PROOF BY SMT

LEMMA EmptyNotIn == \A x : x \notin {}
PROOF BY SMT

LEMMA CSMembers ==
  /\ "cs" \in Numbered
  /\ "cs" \in Waiting
  /\ "cs" \notin Choosing
PROOF BY SMT DEF Choosing, Numbered, Waiting

LEMMA LLAsym == TypeOK => \A i,j \in P :
                   /\ i # j
                   /\ LL(i, j)
                   /\ LL(j, i)
                   => FALSE
PROOF BY SMT, SimpleArithmetic DEF TypeOK, LL, P

LEMMA InitTypeOK == Init => TypeOK
PROOF BY SMT, SetExtensionality DEF Init, TypeOK, PCVals, ProcSet, P

LEMMA InitFlagOK == Init => FlagOK
PROOF BY SMT DEF Init, FlagOK, Choosing, ProcSet, P

LEMMA InitNumOK == Init => NumOK
PROOF BY SMT DEF Init, NumOK, Early, Numbered, ProcSet, P

LEMMA InitUnreadOK == Init => UnreadOK
PROOF BY SMT DEF Init, UnreadOK, ProcSet, P

LEMMA InitPassedOK == Init => PassedOK
PROOF BY SMT DEF Init, PassedOK, Passed, LL, Waiting, ProcSet, P

LEMMA InitDoorOK == Init => DoorOK
PROOF BY SMT DEF Init, DoorOK, LL, Waiting, ProcSet, P

LEMMA InitMaxOK == Init => MaxOK
PROOF BY SMT DEF Init, MaxOK, Waiting, ProcSet, P

LEMMA InitIndInv == Init => IndInv
PROOF BY InitTypeOK, InitFlagOK, InitNumOK, InitUnreadOK,
         InitPassedOK, InitDoorOK, InitMaxOK DEF IndInv

LEMMA CSBothLL == IndInv => \A i,j \in P :
                  /\ i # j
                  /\ pc[i] = "cs"
                  /\ pc[j] = "cs"
                  => /\ LL(i, j)
                     /\ LL(j, i)
PROOF BY SMTT(30), SetExtensionality, EmptyNotIn, CSMembers
       DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK, Passed, LL,
           Choosing, Early, Numbered, Waiting, P

LEMMA CSContradiction == IndInv => \A i,j \in P :
                  /\ i # j
                  /\ pc[i] = "cs"
                  /\ pc[j] = "cs"
                  => FALSE
PROOF
  <1>1. ASSUME IndInv
        PROVE  \A i,j \in P :
                  /\ i # j
                  /\ pc[i] = "cs"
                  /\ pc[j] = "cs"
                  => FALSE
  <2>1. TAKE i,j \in P
  <2>2. ASSUME /\ i # j
                /\ pc[i] = "cs"
                /\ pc[j] = "cs"
          PROVE FALSE
    BY <1>1, <2>1, <2>2, CSBothLL, LLAsym DEF IndInv, TypeOK
  <2>3. QED BY <2>2
  <1>2. QED BY <1>1

LEMMA IndInvMutualExclusion == IndInv => MutualExclusion
PROOF
  BY SMT, CSContradiction DEF MutualExclusion

LEMMA P1TypeOK == \A self \in P : IndInv /\ p1(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p1, PCVals, ProcSet, P

LEMMA P1FlagOK == \A self \in P : IndInv /\ p1(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, FlagOK, p1, Choosing, ProcSet, P

LEMMA P1NumOK == \A self \in P : IndInv /\ p1(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, NumOK, p1, Early, Numbered, ProcSet, P

LEMMA P1UnreadOK == \A self \in P : IndInv /\ p1(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, UnreadOK, p1, ProcSet, P

LEMMA P1PassedOK == \A self \in P : IndInv /\ p1(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
        Passed, LL, Waiting, p1, Choosing, Early, Numbered, ProcSet, P

LEMMA P1DoorOK == \A self \in P : IndInv /\ p1(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK, PassedOK,
        Passed, LL, Waiting, p1, Choosing, Early, Numbered, ProcSet, P

LEMMA P1MaxOK == \A self \in P : IndInv /\ p1(self) => MaxOK'
PROOF BY SMT, ExceptHit, ExceptOther DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, p1, ProcSet, P

LEMMA IndInvP1 == \A self \in P : IndInv /\ p1(self) => IndInv'
PROOF BY P1TypeOK, P1FlagOK, P1NumOK, P1UnreadOK, P1PassedOK,
         P1DoorOK, P1MaxOK DEF IndInv

LEMMA P2TypeOK == \A self \in P : IndInv /\ p2(self) => TypeOK'
PROOF BY SMTT(30), SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p2, PCVals, ProcSet, P

LEMMA P2FlagOK == \A self \in P : IndInv /\ p2(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, p2, Choosing, ProcSet, P

LEMMA P2NumOK == \A self \in P : IndInv /\ p2(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, p2, Early, Numbered, ProcSet, P

LEMMA P2UnreadOK == \A self \in P : IndInv /\ p2(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, p2, ProcSet, P

LEMMA P2PassedOK == \A self \in P : IndInv /\ p2(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, p2, Choosing, Early, Numbered, ProcSet, P

LEMMA P2DoorOK == \A self \in P : IndInv /\ p2(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK,
      Passed, LL, Waiting, p2, Choosing, Early, Numbered, ProcSet, P

LEMMA P2MaxOK == \A self \in P : IndInv /\ p2(self) => MaxOK'
PROOF BY SMTT(30), SimpleArithmetic, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, p2, ProcSet, P

LEMMA IndInvP2 == \A self \in P : IndInv /\ p2(self) => IndInv'
PROOF BY P2TypeOK, P2FlagOK, P2NumOK, P2UnreadOK, P2PassedOK,
         P2DoorOK, P2MaxOK DEF IndInv

LEMMA P3TypeOK == \A self \in P : IndInv /\ p3(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p3, PCVals, ProcSet, P

LEMMA P3FlagOK == \A self \in P : IndInv /\ p3(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, p3, Choosing, ProcSet, P

LEMMA P3NumOK == \A self \in P : IndInv /\ p3(self) => NumOK'
PROOF BY SMT, SimpleArithmetic, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, p3, Early, Numbered, ProcSet, P

LEMMA P3UnreadOK == \A self \in P : IndInv /\ p3(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, p3, ProcSet, P

LEMMA P3PassedOK == \A self \in P : IndInv /\ p3(self) => PassedOK'
PROOF BY SMT, SimpleArithmetic, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, p3, Choosing, Early, Numbered, ProcSet, P

LEMMA P3DoorOK == \A self \in P : IndInv /\ p3(self) => DoorOK'
PROOF BY SMT, SimpleArithmetic, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK, MaxOK,
      Passed, LL, Waiting, p3, Choosing, Early, Numbered, ProcSet, P

LEMMA P3MaxOK == \A self \in P : IndInv /\ p3(self) => MaxOK'
PROOF BY SMT, SimpleArithmetic, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, p3, ProcSet, P

LEMMA IndInvP3 == \A self \in P : IndInv /\ p3(self) => IndInv'
PROOF BY P3TypeOK, P3FlagOK, P3NumOK, P3UnreadOK, P3PassedOK,
         P3DoorOK, P3MaxOK DEF IndInv

LEMMA IndInvP4 == \A self \in P : IndInv /\ p4(self) => IndInv'
PROOF BY SMTT(30), SetExtensionality, ExceptHit, ExceptOther, ExceptFunction,
         SetMinusIntro, SetMinusSelf
  DEF IndInv, TypeOK, FlagOK, NumOK,
        UnreadOK, PassedOK, DoorOK, MaxOK, Passed, LL, PCVals, Choosing,
        Early, Numbered, Waiting, p4, ProcSet, P

LEMMA P5TypeOK == \A self \in P : IndInv /\ p5(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p5, PCVals, ProcSet, P

LEMMA P5FlagOK == \A self \in P : IndInv /\ p5(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, p5, Choosing, ProcSet, P

LEMMA P5NumOK == \A self \in P : IndInv /\ p5(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, p5, Early, Numbered, ProcSet, P

LEMMA P5UnreadOK == \A self \in P : IndInv /\ p5(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, p5, ProcSet, P

LEMMA P5PassedOK == \A self \in P : IndInv /\ p5(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, p5, Choosing, Early, Numbered, ProcSet, P

LEMMA P5DoorOK == \A self \in P : IndInv /\ p5(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK,
      Passed, LL, Waiting, p5, Choosing, Early, Numbered, ProcSet, P

LEMMA P5MaxOK == \A self \in P : IndInv /\ p5(self) => MaxOK'
PROOF BY SMTT(30), ExceptHit, ExceptOther, SetMinusIntro, SetMinusSelf
  DEF IndInv, TypeOK, FlagOK, UnreadOK, MaxOK, Waiting, p5, Choosing,
      ProcSet, P

LEMMA IndInvP5 == \A self \in P : IndInv /\ p5(self) => IndInv'
PROOF BY P5TypeOK, P5FlagOK, P5NumOK, P5UnreadOK, P5PassedOK,
         P5DoorOK, P5MaxOK DEF IndInv

LEMMA P6TypeOK == \A self \in P : IndInv /\ p6(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p6, PCVals, ProcSet, P

LEMMA P6FlagOK == \A self \in P : IndInv /\ p6(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, p6, Choosing, ProcSet, P

LEMMA P6NumOK == \A self \in P : IndInv /\ p6(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, p6, Early, Numbered, ProcSet, P

LEMMA P6UnreadOK == \A self \in P : IndInv /\ p6(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, p6, ProcSet, P

LEMMA P6PassedOK == \A self \in P : IndInv /\ p6(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, p6, Choosing, Early, Numbered, ProcSet, P

LEMMA P6DoorOK == \A self \in P : IndInv /\ p6(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK,
      Passed, LL, Waiting, p6, Choosing, Early, Numbered, ProcSet, P

LEMMA P6MaxOK == \A self \in P : IndInv /\ p6(self) => MaxOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, p6, ProcSet, P

LEMMA IndInvP6 == \A self \in P : IndInv /\ p6(self) => IndInv'
PROOF BY P6TypeOK, P6FlagOK, P6NumOK, P6UnreadOK, P6PassedOK,
         P6DoorOK, P6MaxOK DEF IndInv

LEMMA CSTypeOK == \A self \in P : IndInv /\ cs(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, cs, PCVals, ProcSet, P

LEMMA CSFlagOK == \A self \in P : IndInv /\ cs(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, cs, Choosing, ProcSet, P

LEMMA CSNumOK == \A self \in P : IndInv /\ cs(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, cs, Early, Numbered, ProcSet, P

LEMMA CSUnreadOK == \A self \in P : IndInv /\ cs(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, cs, ProcSet, P

LEMMA CSPassedOK == \A self \in P : IndInv /\ cs(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, cs, Choosing, Early, Numbered, ProcSet, P

LEMMA CSDoorOK == \A self \in P : IndInv /\ cs(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK,
      Passed, LL, Waiting, cs, Choosing, Early, Numbered, ProcSet, P

LEMMA CSMaxOK == \A self \in P : IndInv /\ cs(self) => MaxOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, cs, ProcSet, P

LEMMA IndInvCS == \A self \in P : IndInv /\ cs(self) => IndInv'
PROOF BY CSTypeOK, CSFlagOK, CSNumOK, CSUnreadOK, CSPassedOK,
         CSDoorOK, CSMaxOK DEF IndInv

LEMMA P7TypeOK == \A self \in P : IndInv /\ p7(self) => TypeOK'
PROOF BY SMT, SetExtensionality, ExceptHit, ExceptOther, ExceptFunction
  DEF IndInv, TypeOK, p7, PCVals, ProcSet, P

LEMMA P7FlagOK == \A self \in P : IndInv /\ p7(self) => FlagOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, p7, Choosing, ProcSet, P

LEMMA P7NumOK == \A self \in P : IndInv /\ p7(self) => NumOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, NumOK, p7, Early, Numbered, ProcSet, P

LEMMA P7UnreadOK == \A self \in P : IndInv /\ p7(self) => UnreadOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, p7, ProcSet, P

LEMMA P7PassedOK == \A self \in P : IndInv /\ p7(self) => PassedOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, PassedOK,
      Passed, LL, Waiting, p7, Choosing, Early, Numbered, ProcSet, P

LEMMA P7DoorOK == \A self \in P : IndInv /\ p7(self) => DoorOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK, DoorOK,
      Passed, LL, Waiting, p7, Choosing, Early, Numbered, ProcSet, P

LEMMA P7MaxOK == \A self \in P : IndInv /\ p7(self) => MaxOK'
PROOF BY SMT, ExceptHit, ExceptOther
  DEF IndInv, TypeOK, UnreadOK, MaxOK, Waiting, p7, ProcSet, P

LEMMA IndInvP7 == \A self \in P : IndInv /\ p7(self) => IndInv'
PROOF BY P7TypeOK, P7FlagOK, P7NumOK, P7UnreadOK, P7PassedOK,
         P7DoorOK, P7MaxOK DEF IndInv

LEMMA IndInvNextAction == IndInv /\ Next => IndInv'
PROOF BY IndInvP1, IndInvP2, IndInvP3, IndInvP4, IndInvP5, IndInvP6,
         IndInvCS, IndInvP7 DEF Next, p

LEMMA IndInvStutter == IndInv /\ UNCHANGED vars => IndInv'
PROOF BY SMT DEF IndInv, TypeOK, FlagOK, NumOK, UnreadOK,
                 PassedOK, DoorOK, MaxOK, Passed, LL, vars

LEMMA IndInvNext == IndInv /\ [Next]_vars => IndInv'
PROOF BY IndInvNextAction, IndInvStutter DEF vars

THEOREM Spec => []MutualExclusion
PROOF
  <1>1. Spec => []IndInv
    BY InitIndInv, IndInvNext, PTL DEF Spec
  <1>2. QED BY <1>1, IndInvMutualExclusion, PTL
=============================================================================
