--------------------------- MODULE Peterson_Liveness  ----------------------------

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

Wait(i) == (pc[0] = "a3a") \/ (pc[0] = "a3b")
CS(i) == pc[i] = "cs"
Fairness == WF_vars(proc(0)) /\ WF_vars(proc(1))
FairSpec == Spec /\ Fairness
Liveness == (Wait(0) ~> CS(0)) /\ (Wait(1) ~> CS(1))

-----------------------------------------------------------------------------

USE DEF ProcSet

-----------

TypeOK == /\ flag \in [{0,1} -> BOOLEAN]
          /\ turn \in {0,1}
          /\ pc \in [{0,1} -> {"a0","a1","a2","a3a","a3b","cs","a4"}]

FlagInv == \A i \in {0,1} : flag[i] = (pc[i] \in {"a2","a3a","a3b","cs","a4"})

Inv == TypeOK /\ FlagInv

LEMMA Inv_Inv == Spec => []Inv
<1>1. Init => Inv BY DEF Init, Inv, TypeOK, FlagInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

(* Single-step transition lemmas using proc(i) WF *)

LEMMA L_a0 == \A i \in {0,1} : Spec => (pc[i] = "a0") ~> (pc[i] = "a1")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a0"
<1> DEFINE Q == pc[i] = "a1"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a1 == \A i \in {0,1} : Spec => (pc[i] = "a1") ~> (pc[i] = "a2")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a1"
<1> DEFINE Q == pc[i] = "a2"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a2 == \A i \in {0,1} : Spec => (pc[i] = "a2") ~> (pc[i] = "a3a")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a2"
<1> DEFINE Q == pc[i] = "a3a"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_cs == \A i \in {0,1} : Spec => (pc[i] = "cs") ~> (pc[i] = "a4")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "cs"
<1> DEFINE Q == pc[i] = "a4"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a4 == \A i \in {0,1} : Spec => (pc[i] = "a4") ~> (pc[i] = "a0")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a4"
<1> DEFINE Q == pc[i] = "a0"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

(* Cycle-breaking lemmas via proc(i) when turn favors i *)

LEMMA L_a3b_turn_self == \A i \in {0,1} : 
  Spec => (pc[i] = "a3b" /\ turn = i) ~> (pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a3b" /\ turn = i
<1> DEFINE Q == pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a3a_turn_self == \A i \in {0,1} :
  Spec => (pc[i] = "a3a" /\ turn = i) ~>
          ((pc[i] = "a3b" /\ turn = i) \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ pc[i] = "a3a" /\ turn = i
<1> DEFINE Q == (pc[i] = "a3b" /\ turn = i) \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(i)>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(i)>>_vars
  <2> SUFFICES ASSUME P PROVE ENABLED <<proc(i)>>_vars
    OBVIOUS
  <2>1. CASE flag[Not(i)]
    BY <2>1, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>2. CASE ~flag[Not(i)]
    BY <2>2, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>3. QED BY <2>1, <2>2
<1>4. [][Next]_vars /\ WF_vars(proc(i)) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_turn_self == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) ~> (pc[i] = "cs")
<1> TAKE i \in {0,1}
<1>1. Spec => (pc[i] = "a3a" /\ turn = i) ~> ((pc[i] = "a3b" /\ turn = i) \/ pc[i] = "cs")
  BY L_a3a_turn_self
<1>2. Spec => (pc[i] = "a3b" /\ turn = i) ~> (pc[i] = "cs")
  BY L_a3b_turn_self
<1>3. QED BY <1>1, <1>2, PTL

(* Process j (= Not(i)) progression lemmas -
   when pc[i] is waiting in {a3a, a3b}, process j moves forward.
   These use proc(Not(i)) WF. *)

LEMMA L_a0_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a1_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a2_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a3a_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME P PROVE ENABLED <<proc(Not(i))>>_vars
    OBVIOUS
  <2>0. flag[i] /\ Not(Not(i)) = i BY DEF Inv, TypeOK, FlagInv, Not
  <2>1. CASE i = 0
    BY <2>0, <2>1, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>2. CASE i = 1
    BY <2>0, <2>2, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>3. QED BY <2>1, <2>2
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a3b_turn_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = Not(i)) ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = Not(i)
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  <2> SUFFICES ASSUME P PROVE ENABLED <<proc(Not(i))>>_vars
    OBVIOUS
  <2>1. CASE turn = Not(Not(i))
    BY <2>1, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>2. CASE turn # Not(Not(i))
    BY <2>2, ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
  <2>3. QED BY <2>1, <2>2
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_cs_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

LEMMA L_a4_other == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") ~>
          (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") \/ pc[i] = "cs")
<1> TAKE i \in {0,1}
<1> DEFINE P == Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4"
<1> DEFINE Q == ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") \/ pc[i] = "cs"
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>2. P /\ <<Next /\ proc(Not(i))>>_vars => Q'
  BY DEF Inv, TypeOK, FlagInv, Next, vars, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>3. P => ENABLED <<proc(Not(i))>>_vars
  BY ExpandENABLED DEF Inv, TypeOK, FlagInv, proc, a0, a1, a2, a3a, a3b, cs, a4, vars, Not
<1>4. [][Next]_vars /\ WF_vars(proc(Not(i))) => (P ~> Q)
  BY <1>1, <1>2, <1>3, PTL
<1>5. Spec => P ~> Q
  BY <1>4 DEF Spec, Not
<1>6. QED BY <1>5, Inv_Inv, PTL

(* Chain lemmas: pc[i] = a3a/a3b /\ pc[Not(i)] = X ~> pc[i] = cs *)

LEMMA LL_other_a2 == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) \/ pc[i] = "cs")
  BY L_a2_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) ~> pc[i] = "cs"
  BY L_turn_self
<1>3. QED BY <1>1, <1>2, PTL

LEMMA LL_other_a1 == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") \/ pc[i] = "cs")
  BY L_a1_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") ~> pc[i] = "cs"
  BY LL_other_a2
<1>3. QED BY <1>1, <1>2, PTL

LEMMA LL_other_a0 == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") \/ pc[i] = "cs")
  BY L_a0_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") ~> pc[i] = "cs"
  BY LL_other_a1
<1>3. QED BY <1>1, <1>2, PTL

LEMMA LL_other_a4 == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") \/ pc[i] = "cs")
  BY L_a4_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") ~> pc[i] = "cs"
  BY LL_other_a0
<1>3. QED BY <1>1, <1>2, PTL

LEMMA LL_other_cs == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") \/ pc[i] = "cs")
  BY L_cs_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") ~> pc[i] = "cs"
  BY LL_other_a4
<1>3. QED BY <1>1, <1>2, PTL

LEMMA LL_other_a3b == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = Not(i)) ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") \/ pc[i] = "cs")
  BY L_a3b_turn_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") ~> pc[i] = "cs"
  BY LL_other_cs
<1>3. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ turn = i) ~> pc[i] = "cs"
  BY L_turn_self
<1>4. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = Not(i)) ~> pc[i] = "cs"
  BY <1>1, <1>2, PTL
<1>5. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = i) ~> pc[i] = "cs"
  BY <1>3, PTL
<1>6. Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" =>
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = Not(i)) \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b" /\ turn = i)
  BY DEF Inv, TypeOK, Not
<1>7. QED BY <1>4, <1>5, <1>6, Inv_Inv, PTL

LEMMA LL_other_a3a == \A i \in {0,1} :
  Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a") ~>
        (((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") \/ pc[i] = "cs")
  BY L_a3a_other
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") ~> pc[i] = "cs"
  BY LL_other_a3b
<1>3. QED BY <1>1, <1>2, PTL

(* Final cycle break: combines all 7 cases of pc[Not(i)] via disjunction *)

LEMMA Cycle_Break == \A i \in {0,1} :
  Spec => (pc[i] = "a3a" \/ pc[i] = "a3b") ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") ~> pc[i] = "cs" BY LL_other_a0
<1>2. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") ~> pc[i] = "cs" BY LL_other_a1
<1>3. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") ~> pc[i] = "cs" BY LL_other_a2
<1>4. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a") ~> pc[i] = "cs" BY LL_other_a3a
<1>5. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") ~> pc[i] = "cs" BY LL_other_a3b
<1>6. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") ~> pc[i] = "cs" BY LL_other_cs
<1>7. Spec => ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4") ~> pc[i] = "cs" BY LL_other_a4
<1>8. Inv /\ (pc[i] = "a3a" \/ pc[i] = "a3b") =>
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a0") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a1") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a2") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3a") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a3b") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "cs") \/
        ((pc[i] = "a3a" \/ pc[i] = "a3b") /\ pc[Not(i)] = "a4")
  BY DEF Inv, TypeOK, Not
<1>9. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, Inv_Inv, PTL

(* TRUE ~> pc[i] = cs: process i always eventually reaches cs *)

LEMMA L_all_to_cs == \A i \in {0,1} : Spec => TRUE ~> pc[i] = "cs"
<1> TAKE i \in {0,1}
<1>1. Spec => (pc[i] = "a3a" \/ pc[i] = "a3b") ~> pc[i] = "cs" BY Cycle_Break
<1>2. Spec => pc[i] = "a0" ~> pc[i] = "a1" BY L_a0
<1>3. Spec => pc[i] = "a1" ~> pc[i] = "a2" BY L_a1
<1>4. Spec => pc[i] = "a2" ~> pc[i] = "a3a" BY L_a2
<1>5. Spec => pc[i] = "cs" ~> pc[i] = "a4" BY L_cs
<1>6. Spec => pc[i] = "a4" ~> pc[i] = "a0" BY L_a4
<1>7. Inv => (pc[i] = "a0" \/ pc[i] = "a1" \/ pc[i] = "a2" \/
              pc[i] = "a3a" \/ pc[i] = "a3b" \/ pc[i] = "cs" \/ pc[i] = "a4")
  BY DEF Inv, TypeOK
<1>8. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Inv_Inv, PTL

(* Helper operator: Live(i) is the leads-to we want for process i *)
Live(i) == Wait(i) ~> CS(i)

LEMMA L_Live_All == \A i \in {0,1} : Spec => Live(i)
<1> TAKE i \in {0,1}
<1>1. Spec => TRUE ~> pc[i] = "cs" BY L_all_to_cs
<1>2. Spec => Live(i) BY <1>1, PTL DEF Live, Wait, CS
<1>3. QED BY <1>2

LEMMA L_Live_Conj == Spec => Live(0) /\ Live(1)
  BY L_Live_All

THEOREM FairSpec => Liveness
<1>1. Spec => Live(0) /\ Live(1) BY L_Live_Conj
<1>2. QED BY <1>1, PTL DEF FairSpec, Liveness, Live
=============================================================================
