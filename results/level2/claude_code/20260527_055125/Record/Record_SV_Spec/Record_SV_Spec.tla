------------------------------- MODULE Record_SV_Spec -------------------------------

EXTENDS Naturals, TLAPS
---------------------------------------------------------------------------
CONSTANTS Participant

VARIABLES state

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

maxBal == [p \in Participant |-> state[p][p].maxBal]

SV == INSTANCE SimpleVoting

(*****************************************************************************)
(* Type invariant on `state`.                                                *)
(*****************************************************************************)
TypeOK == state \in [Participant -> [Participant -> [maxBal: Nat, maxVBal: Nat]]]

LEMMA InitTypeOK == Init => TypeOK
  <1> SUFFICES ASSUME Init PROVE TypeOK OBVIOUS
  <1>1. InitState \in [maxBal: Nat, maxVBal: Nat]
    BY DEF InitState
  <1>2. [q \in Participant |-> InitState] \in [Participant -> [maxBal: Nat, maxVBal: Nat]]
    BY <1>1
  <1>3. state = [p \in Participant |-> [q \in Participant |-> InitState]]
    BY DEF Init
  <1>4. state \in [Participant -> [Participant -> [maxBal: Nat, maxVBal: Nat]]]
    BY <1>2, <1>3
  <1> QED BY <1>4 DEF TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_state => TypeOK'
  <1> SUFFICES ASSUME TypeOK, [Next]_state PROVE TypeOK' OBVIOUS
  <1>1. CASE Next
    <2>1. PICK p \in Participant, b \in Nat : Prepare(p, b)
      BY <1>1 DEF Next
    <2>2. state' = [state EXCEPT ![p][p].maxBal = b]
      BY <2>1 DEF Prepare
    <2>3. state[p] \in [Participant -> [maxBal: Nat, maxVBal: Nat]]
      BY DEF TypeOK
    <2>4. state[p][p] \in [maxBal: Nat, maxVBal: Nat]
      BY <2>3
    <2>5. [state[p][p] EXCEPT !.maxBal = b] \in [maxBal: Nat, maxVBal: Nat]
      BY <2>4
    <2>6. [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]] \in [Participant -> [maxBal: Nat, maxVBal: Nat]]
      BY <2>5, <2>3
    <2>7. state' = [state EXCEPT ![p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]]
      BY <2>2
    <2>8. state' \in [Participant -> [Participant -> [maxBal: Nat, maxVBal: Nat]]]
      BY <2>6, <2>7 DEF TypeOK
    <2> QED BY <2>8 DEF TypeOK
  <1>2. CASE UNCHANGED state
    BY <1>2 DEF TypeOK
  <1> QED BY <1>1, <1>2

LEMMA InitImpl == Init => SV!Init
  <1> SUFFICES ASSUME Init PROVE SV!Init OBVIOUS
  <1>1. state = [p \in Participant |-> [q \in Participant |-> InitState]]
    BY DEF Init
  <1>2. \A p \in Participant : state[p][p] = InitState
    BY <1>1
  <1>3. \A p \in Participant : state[p][p].maxBal = 0
    BY <1>2 DEF InitState
  <1>4. maxBal = [p \in Participant |-> 0]
    BY <1>3 DEF maxBal
  <1> QED BY <1>4 DEF SV!Init

LEMMA NextImpl == TypeOK /\ [Next]_state => [SV!Next]_maxBal
  <1> SUFFICES ASSUME TypeOK, [Next]_state PROVE [SV!Next]_maxBal OBVIOUS
  <1>1. CASE Next
    <2>1. PICK p \in Participant, b \in Nat : Prepare(p, b)
      BY <1>1 DEF Next
    <2>2. state[p][p].maxBal < b
      BY <2>1 DEF Prepare
    <2>3. state' = [state EXCEPT ![p][p].maxBal = b]
      BY <2>1 DEF Prepare
    <2>4. state[p] \in [Participant -> [maxBal: Nat, maxVBal: Nat]]
      BY DEF TypeOK
    <2>5. state[p][p] \in [maxBal: Nat, maxVBal: Nat]
      BY <2>4
    <2>6. state[p][p].maxBal \in Nat
      BY <2>5
    <2>7. state' = [state EXCEPT ![p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]]
      BY <2>3
    <2>8. state'[p] = [state[p] EXCEPT ![p] = [state[p][p] EXCEPT !.maxBal = b]]
      BY <2>7 DEF TypeOK
    <2>9. state'[p][p] = [state[p][p] EXCEPT !.maxBal = b]
      BY <2>8, <2>4
    <2>10. state'[p][p].maxBal = b
      BY <2>9, <2>5
    <2>11. ASSUME NEW q \in Participant, q # p
           PROVE state'[q][q].maxBal = state[q][q].maxBal
      <3>1. state'[q] = state[q]
        BY <2>7, <2>11 DEF TypeOK
      <3> QED BY <3>1
    <2>12. \A p2 \in Participant : state'[p2][p2].maxBal =
              (IF p2 = p THEN b ELSE state[p2][p2].maxBal)
      <3>1. TAKE p2 \in Participant
      <3>2. CASE p2 = p
        BY <3>2, <2>10
      <3>3. CASE p2 # p
        BY <3>3, <2>11
      <3> QED BY <3>2, <3>3
    <2>13. [p2 \in Participant |-> state'[p2][p2].maxBal] =
           [p2 \in Participant |-> (IF p2 = p THEN b ELSE state[p2][p2].maxBal)]
      BY <2>12
    <2>14. maxBal' = [p2 \in Participant |-> state'[p2][p2].maxBal]
      BY DEF maxBal
    <2>15. maxBal = [p2 \in Participant |-> state[p2][p2].maxBal]
      BY DEF maxBal
    <2>16. [maxBal EXCEPT ![p] = b] =
           [p2 \in Participant |-> (IF p2 = p THEN b ELSE state[p2][p2].maxBal)]
      <3>1. DOMAIN maxBal = Participant
        BY <2>15
      <3>2. [maxBal EXCEPT ![p] = b] =
            [p2 \in DOMAIN maxBal |-> IF p2 = p THEN b ELSE maxBal[p2]]
        OBVIOUS
      <3>3. \A p2 \in Participant : maxBal[p2] = state[p2][p2].maxBal
        BY <2>15
      <3> QED BY <3>1, <3>2, <3>3
    <2>17. maxBal' = [maxBal EXCEPT ![p] = b]
      BY <2>13, <2>14, <2>16
    <2>18. maxBal[p] = state[p][p].maxBal
      BY <2>15
    <2>19. maxBal[p] < b
      BY <2>2, <2>18
    <2>20. SV!IncreaseMaxBal(p, b)
      BY <2>17, <2>19 DEF SV!IncreaseMaxBal
    <2> QED BY <2>20 DEF SV!Next
  <1>2. CASE UNCHANGED state
    <2>1. maxBal' = maxBal
      BY <1>2 DEF maxBal
    <2> QED BY <2>1
  <1> QED BY <1>1, <1>2

THEOREM Spec => SV!Spec
<1>1. Init => SV!Init BY InitImpl
<1>2. Spec => []TypeOK
  BY InitTypeOK, NextTypeOK, PTL DEF Spec
<1>3. Spec => [][SV!Next]_maxBal
  BY <1>2, NextImpl, PTL DEF Spec
<1>4. QED BY <1>1, <1>3, PTL DEF Spec, SV!Spec
=============================================================================

