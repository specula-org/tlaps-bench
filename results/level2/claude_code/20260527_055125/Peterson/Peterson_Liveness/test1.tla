--------------------------- MODULE test1  ----------------------------

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

USE DEF ProcSet

TypeOK == /\ flag \in [{0,1} -> BOOLEAN]
          /\ turn \in {0,1}
          /\ pc \in [{0,1} -> {"a0","a1","a2","a3a","a3b","cs","a4"}]

LEMMA TypeOKInv == Spec => []TypeOK
<1>1. Init => TypeOK BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

LEMMA L_a0_0 == Spec => (pc[0] = "a0") ~> (pc[0] = "a1")
<1> DEFINE P == TypeOK /\ pc[0] = "a0"
<1> DEFINE Q == pc[0] = "a1"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF TypeOK, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(0)>>_vars => Q'
  BY DEF TypeOK, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(0)>>_vars
  BY ExpandENABLED DEF TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(0)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec
<1>6. QED 
  BY <1>5, TypeOKInv, PTL

THEOREM TRUE PROOF OBVIOUS
=============================================================================
