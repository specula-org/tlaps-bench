--------------------------- MODULE Peterson_MutualExclusion  ----------------------------

EXTENDS TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init ==
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag

a3a(self) == /\ pc[self] = "a3a"
             /\ IF flag[Not(self)]
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

a3b(self) == /\ pc[self] = "a3b"
             /\ IF turn = Not(self)
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

-----------------------------------------------------------------------------

USE DEF ProcSet

TypeOK ==
    /\ flag \in [{0,1} -> BOOLEAN]
    /\ turn \in {0,1}
    /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]

IndInv ==
    /\ TypeOK
    /\ \A i \in {0,1} :
         (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"}) <=> (flag[i] = TRUE)
    /\ \A i \in {0,1} :
         pc[i] \in {"cs", "a4"} =>
           \/ pc[Not(i)] \in {"a0", "a1", "a2"}
           \/ (pc[Not(i)] \in {"a3a", "a3b"} /\ turn = i)

LEMMA InitImpliesIndInv == Init => IndInv
<1> SUFFICES ASSUME Init PROVE IndInv OBVIOUS
<1> QED BY DEF Init, IndInv, TypeOK, Not

LEMMA IndInvImpliesME == IndInv => MutualExclusion
<1> SUFFICES ASSUME IndInv, pc[0] = "cs", pc[1] = "cs" PROVE FALSE
  BY DEF MutualExclusion
<1>1. pc[Not(0)] \in {"a0", "a1", "a2"} \/ (pc[Not(0)] \in {"a3a", "a3b"} /\ turn = 0)
  BY DEF IndInv
<1>2. Not(0) = 1 BY DEF Not
<1> QED BY <1>1, <1>2

LEMMA IndInvIsInductive == IndInv /\ [Next]_vars => IndInv'
<1> SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv' OBVIOUS
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF IndInv, TypeOK, vars
<1>2. CASE Next
  <2> PICK self \in {0,1} : proc(self) BY <1>2 DEF Next
  <2>0. self \in {0,1} OBVIOUS
  <2>1. Not(self) \in {0,1} /\ Not(self) # self BY DEF Not
  <2>2. CASE a0(self)
    BY <2>2, <2>0, <2>1 DEF a0, IndInv, TypeOK, Not
  <2>3. CASE a1(self)
    BY <2>3, <2>0, <2>1 DEF a1, IndInv, TypeOK, Not
  <2>4. CASE a2(self)
    BY <2>4, <2>0, <2>1 DEF a2, IndInv, TypeOK, Not
  <2>5. CASE a3a(self)
    BY <2>5, <2>0, <2>1 DEF a3a, IndInv, TypeOK, Not
  <2>6. CASE a3b(self)
    BY <2>6, <2>0, <2>1 DEF a3b, IndInv, TypeOK, Not
  <2>7. CASE cs(self)
    BY <2>7, <2>0, <2>1 DEF cs, IndInv, TypeOK, Not
  <2>8. CASE a4(self)
    BY <2>8, <2>0, <2>1 DEF a4, IndInv, TypeOK, Not
  <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF proc
<1> QED BY <1>1, <1>2

THEOREM Spec => []MutualExclusion
<1>1. Init => IndInv BY InitImpliesIndInv
<1>2. IndInv /\ [Next]_vars => IndInv' BY IndInvIsInductive
<1>3. IndInv => MutualExclusion BY IndInvImpliesME
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

-----------

=============================================================================
