------------------------------- MODULE Record_SV_Spec -------------------------------
(*
It is necessary to use type invariant when reasoning about EXCEPT expressions.
See step <4>2 in the proof for Spec => SV!Spec.

See https://groups.google.com/d/msg/tlaplus/rmmH9vFwH_0/rY18YWMGDQAJ.
*)
EXTENDS Naturals, TLAPS
---------------------------------------------------------------------------
CONSTANTS Participant  \* the set of partipants

VARIABLES state \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    
State == [maxBal: Nat, maxVBal: Nat]

TypeOK == state \in [Participant -> [Participant -> State]]
---------------------------------------------------------------------------
InitState == [maxBal |-> 0, maxVBal |-> 0]

Init == state = [p \in Participant |-> [q \in Participant |-> InitState]] 

Prepare(p, b) == 
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
---------------------------------------------------------------------------
Next == \E p \in Participant, b \in Nat : Prepare(p, b)

Spec == Init /\ [][Next]_state
---------------------------------------------------------------------------
(*
Record refines SimpleVoting
*)
maxBal == [p \in Participant |-> state[p][p].maxBal]

SV == INSTANCE SimpleVoting


LEMMA InitTypeOK == Init => TypeOK
BY DEF Init, TypeOK, State, InitState

LEMMA NextTypeOK == TypeOK /\ [Next]_state => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_state PROVE TypeOK'
  OBVIOUS
<1>1. CASE Next
  <2> SUFFICES ASSUME NEW p \in Participant, NEW b \in Nat, Prepare(p, b)
                PROVE  TypeOK'
    BY <1>1 DEF Next
  <2>1. state[p][p].maxBal < b /\ state' = [state EXCEPT ![p][p].maxBal = b]
    BY DEF Prepare
  <2>2. state \in [Participant -> [Participant -> State]]
    BY DEF TypeOK
  <2>3. \A q \in Participant : state[p][q] \in State
    BY <2>2
  <2>4. [state[p][p] EXCEPT !.maxBal = b] \in State
    BY <2>3, b \in Nat DEF State
  <2>5. [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]] \in [Participant -> State]
    BY <2>2, <2>4
  <2>6. state' = [state EXCEPT ![p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]]
    BY <2>1
  <2>7. state' \in [Participant -> [Participant -> State]]
    BY <2>2, <2>5, <2>6
  <2> QED
    BY <2>7 DEF TypeOK
<1>2. CASE state' = state
  BY <1>2 DEF TypeOK
<1> QED
  BY <1>1, <1>2 DEF Next

LEMMA InitRefine == Init => SV!Init
BY DEF Init, SV!Init, maxBal, InitState

LEMMA NextRefine == TypeOK /\ [Next]_state => [SV!Next]_maxBal
<1> SUFFICES ASSUME TypeOK, [Next]_state PROVE [SV!Next]_maxBal
  OBVIOUS
<1> state \in [Participant -> [Participant -> State]]
  BY DEF TypeOK
<1>1. CASE Next
  <2> SUFFICES ASSUME NEW p \in Participant, NEW b \in Nat, Prepare(p, b)
                PROVE  SV!Next
    BY <1>1 DEF Next, SV!Next
  <2>1. state[p][p].maxBal < b /\ state' = [state EXCEPT ![p][p].maxBal = b]
    BY DEF Prepare
  <2>2. \A q \in Participant : state[p][q] \in State /\ state[p][q].maxBal \in Nat
    BY DEF TypeOK, State
  <2>3. maxBal[p] < b
    BY <2>1, <2>2 DEF maxBal
  <2>4. state' = [state EXCEPT ![p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]]
    BY <2>1
  <2>5. ASSUME NEW q \in Participant
        PROVE  state'[q][q].maxBal = IF q = p THEN b ELSE state[q][q].maxBal
    <3>1. CASE q = p
      <4>1. state'[p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]
        BY <2>4
      <4>2. state'[p][p] = [state[p][p] EXCEPT !.maxBal = b]
        BY <4>1
      <4>3. state'[p][p].maxBal = b
        BY <4>2, <2>2 DEF State
      <4> QED
        BY <4>3, <3>1
    <3>2. CASE q # p
      <4>1. state'[q] = state[q]
        BY <2>4, <3>2
      <4> QED
        BY <4>1, <3>2
    <3> QED
      BY <3>1, <3>2
  <2>6. maxBal' = [q \in Participant |-> IF q = p THEN b ELSE state[q][q].maxBal]
    BY <2>5 DEF maxBal
  <2>7. maxBal = [q \in Participant |-> state[q][q].maxBal]
    BY DEF maxBal
  <2>8. maxBal' = [maxBal EXCEPT ![p] = b]
    BY <2>6, <2>7, <2>2
  <2>9. SV!IncreaseMaxBal(p, b)
    BY <2>3, <2>8 DEF SV!IncreaseMaxBal
  <2> QED
    BY <2>9, p \in Participant, b \in Nat DEF SV!Next
<1>2. CASE state' = state
  <2>1. maxBal' = maxBal
    BY <1>2 DEF maxBal
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2 DEF Next

THEOREM Spec => SV!Spec
<1>1. Spec => []TypeOK
  BY InitTypeOK, NextTypeOK, PTL DEF Spec
<1>2. QED
  BY <1>1, InitRefine, NextRefine, PTL DEF Spec, SV!Spec
=============================================================================
\* Modification History
\* Last modified Tue Aug 20 10:52:14 CST 2019 by hengxin
\* Created Thu Aug 15 10:52:49 CST 2019 by hengxin