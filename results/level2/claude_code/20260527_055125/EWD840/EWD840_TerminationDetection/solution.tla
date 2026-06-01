------------------------------- MODULE EWD840_TerminationDetection -------------------------------
EXTENDS Naturals, TLAPS

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Controlled ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)

Environment == \E i \in Nodes : Deactivate(i) \/ SendMsg(i)

Next == Controlled \/ Environment

vars == <<active, color, tpos, tcolor>>

Fairness == WF_vars(Controlled)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

-----------------------------------------------------------------------------

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

IndInv ==
  /\ TypeOK
  /\ \/ \A i \in (tpos+1)..(N-1) : ~active[i]
     \/ \E j \in 0..tpos : color[j] = "black"
     \/ tcolor = "black"

LEMMA InitInv == Init => IndInv
  <1> USE NAssumption
  <1> SUFFICES ASSUME Init PROVE IndInv
    OBVIOUS
  <1> USE DEF Init, IndInv, TypeOK, Nodes, Color
  <1>1. active \in [Nodes -> BOOLEAN] OBVIOUS
  <1>2. color \in [Nodes -> Color] OBVIOUS
  <1>3. tpos \in Nodes
    <2>1. tpos = 0 OBVIOUS
    <2>2. 0 \in 0..(N-1) OBVIOUS
    <2> QED BY <2>1, <2>2
  <1>4. tcolor \in Color OBVIOUS
  <1>5. tcolor = "black" OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA InvImpliesTermDet == IndInv => TerminationDetection
  <1> USE NAssumption DEF IndInv, TypeOK, Nodes, Color, terminationDetected
  <1> SUFFICES ASSUME IndInv, terminationDetected
              PROVE \A k \in Nodes : ~active[k]
    BY DEF TerminationDetection
  <1>1. tpos = 0 /\ tcolor = "white" /\ color[0] = "white" /\ ~active[0]
    OBVIOUS
  <1>2. \A k \in (tpos+1)..(N-1) : ~active[k]
    <2>1. ~(tcolor = "black") BY <1>1
    <2>2. ~(\E j \in 0..tpos : color[j] = "black")
      <3>1. tpos = 0 BY <1>1
      <3>2. color[0] # "black" BY <1>1
      <3>3. 0..tpos = {0} BY <3>1
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>1, <2>2
  <1>3. TAKE k \in Nodes
  <1>4. CASE k = 0 BY <1>1, <1>4
  <1>5. CASE k # 0
    <2>1. k \in 1..(N-1) BY <1>5
    <2>2. k \in (tpos+1)..(N-1) BY <2>1, <1>1
    <2> QED BY <2>2, <1>2
  <1> QED BY <1>4, <1>5

LEMMA InvIsInductive == IndInv /\ [Next]_vars => IndInv'
  <1> USE NAssumption DEF IndInv, TypeOK, Nodes, Color
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
    OBVIOUS

  <1>1. CASE UNCHANGED vars
    <2> USE <1>1 DEF vars
    <2> QED OBVIOUS

  <1>2. CASE InitiateProbe
    <2> USE <1>2 DEF InitiateProbe
    <2>1. active' \in [Nodes -> BOOLEAN] OBVIOUS
    <2>2. color' \in [Nodes -> Color]
      <3>1. color \in [Nodes -> Color] OBVIOUS
      <3>2. 0 \in Nodes OBVIOUS
      <3>3. "white" \in Color OBVIOUS
      <3> QED BY <3>1, <3>2, <3>3
    <2>3. tpos' \in Nodes
      <3>1. tpos' = N - 1 OBVIOUS
      <3>2. N - 1 \in 0..(N-1) OBVIOUS
      <3> QED BY <3>1, <3>2
    <2>4. tcolor' \in Color OBVIOUS
    <2>5. (tpos' + 1)..(N - 1) = {}
      <3>1. tpos' = N - 1 OBVIOUS
      <3>2. tpos' + 1 = N BY <3>1
      <3>3. N..(N-1) = {} OBVIOUS
      <3> QED BY <3>2, <3>3
    <2>6. \A k \in (tpos' + 1)..(N - 1) : ~active'[k] BY <2>5
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>6

  <1>3. CASE \E i \in Nodes \ {0} : PassToken(i)
    <2>pick. PICK i \in Nodes \ {0} : PassToken(i) BY <1>3
    <2> USE <2>pick DEF PassToken
    <2>0. i \in 1..(N-1) OBVIOUS
    <2>1. i \in Nat OBVIOUS
    <2>2. i - 1 \in 0..(N-1) BY <2>0
    <2>3. tpos = i OBVIOUS
    <2>4. tpos' = i - 1 OBVIOUS
    <2>5. active' = active OBVIOUS
    <2>6. color' = [color EXCEPT ![i] = "white"] OBVIOUS
    <2>7. active' \in [Nodes -> BOOLEAN] BY <2>5
    <2>8. color' \in [Nodes -> Color]
      <3>1. color \in [Nodes -> Color] OBVIOUS
      <3>2. i \in Nodes OBVIOUS
      <3>3. "white" \in Color OBVIOUS
      <3> QED BY <3>1, <3>2, <3>3, <2>6
    <2>9. tpos' \in Nodes BY <2>2, <2>4
    <2>10. tcolor' \in Color
      <3>1. tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor OBVIOUS
      <3>2. "black" \in Color OBVIOUS
      <3>3. tcolor \in Color OBVIOUS
      <3> QED BY <3>1, <3>2, <3>3
    <2>11. CASE color[i] = "black"
      <3>1. tcolor' = "black" BY <2>11
      <3> QED BY <3>1, <2>7, <2>8, <2>9, <2>10
    <2>12. CASE color[i] # "black"
      <3>1. tcolor' = tcolor BY <2>12
      <3>2. CASE tcolor = "black"
        <4>1. tcolor' = "black" BY <3>1, <3>2
        <4> QED BY <4>1, <2>7, <2>8, <2>9, <2>10
      <3>3. CASE tcolor # "black"
        <4>1. ~active[i]
          <5>1. ~ active[i] \/ color[i] = "black" \/ tcolor = "black" OBVIOUS
          <5> QED BY <5>1, <3>3, <2>12
        <4>2. ~(tcolor = "black") BY <3>3
        <4>3. \/ \A k \in (tpos+1)..(N-1) : ~active[k]
              \/ \E j \in 0..tpos : color[j] = "black"
              \/ tcolor = "black"
          OBVIOUS
        <4>4. CASE \E j \in 0..tpos : color[j] = "black"
          <5>1. PICK j \in 0..tpos : color[j] = "black" BY <4>4
          <5>2. j \in 0..i BY <5>1, <2>3
          <5>3. j # i BY <5>1, <2>12
          <5>4. j \in 0..(i - 1) BY <5>2, <5>3
          <5>5. j \in Nodes BY <5>4, <2>2
          <5>6. color'[j] = color[j] BY <5>3, <2>6, <5>5
          <5>7. color'[j] = "black" BY <5>6, <5>1
          <5>8. j \in 0..tpos' BY <5>4, <2>4
          <5>9. \E m \in 0..tpos' : color'[m] = "black" BY <5>7, <5>8
          <5> QED BY <5>9, <2>7, <2>8, <2>9, <2>10
        <4>5. CASE \A k \in (tpos + 1)..(N-1) : ~active[k]
          <5>1. \A k \in (i+1)..(N-1) : ~active[k] BY <4>5, <2>3
          <5>2. \A k \in i..(N-1) : ~active[k]
            <6>1. TAKE k \in i..(N-1)
            <6>2. CASE k = i BY <4>1, <6>2
            <6>3. CASE k # i
              <7>1. k \in (i+1)..(N-1) BY <6>3
              <7> QED BY <7>1, <5>1
            <6> QED BY <6>2, <6>3
          <5>3. \A k \in (tpos'+1)..(N-1) : ~active[k] BY <5>2, <2>4
          <5>4. \A k \in (tpos'+1)..(N-1) : ~active'[k] BY <5>3, <2>5
          <5> QED BY <5>4, <2>7, <2>8, <2>9, <2>10
        <4> QED BY <4>2, <4>3, <4>4, <4>5
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>11, <2>12

  <1>4. CASE \E i \in Nodes : Deactivate(i)
    <2>pick. PICK i \in Nodes : Deactivate(i) BY <1>4
    <2> USE <2>pick DEF Deactivate
    <2>1. active' = [active EXCEPT ![i] = FALSE] OBVIOUS
    <2>2. color' = color /\ tpos' = tpos /\ tcolor' = tcolor
      OBVIOUS
    <2>3. active' \in [Nodes -> BOOLEAN]
      <3>1. active \in [Nodes -> BOOLEAN] OBVIOUS
      <3>2. FALSE \in BOOLEAN OBVIOUS
      <3> QED BY <3>1, <3>2, <2>1
    <2>4. tpos' \in Nodes BY <2>2
    <2>5. tcolor' \in Color BY <2>2
    <2>6. color' \in [Nodes -> Color] BY <2>2
    <2>7. CASE \E j \in 0..tpos : color[j] = "black"
      <3>1. PICK j \in 0..tpos : color[j] = "black" BY <2>7
      <3>2. color'[j] = "black" BY <3>1, <2>2
      <3>3. j \in 0..tpos' BY <3>1, <2>2
      <3>4. \E m \in 0..tpos' : color'[m] = "black" BY <3>2, <3>3
      <3> QED BY <3>4, <2>3, <2>4, <2>5, <2>6
    <2>8. CASE tcolor = "black"
      <3>1. tcolor' = "black" BY <2>2, <2>8
      <3> QED BY <3>1, <2>3, <2>4, <2>5, <2>6
    <2>9. CASE \A k \in (tpos + 1)..(N-1) : ~active[k]
      <3>1. \A k \in (tpos' + 1)..(N-1) : ~active'[k]
        <4>1. TAKE k \in (tpos' + 1)..(N-1)
        <4>2. k \in (tpos + 1)..(N-1) BY <2>2
        <4>3. ~active[k] BY <4>2, <2>9
        <4>4. k \in Nodes BY <4>2
        <4>5. CASE k = i
          <5>1. active'[k] = FALSE BY <2>1, <4>4, <4>5
          <5> QED BY <5>1
        <4>6. CASE k # i
          <5>1. active'[k] = active[k] BY <2>1, <4>4, <4>6
          <5> QED BY <5>1, <4>3
        <4> QED BY <4>5, <4>6
      <3> QED BY <3>1, <2>3, <2>4, <2>5, <2>6
    <2>10. \/ \A k \in (tpos+1)..(N-1) : ~active[k]
           \/ \E j \in 0..tpos : color[j] = "black"
           \/ tcolor = "black"
      OBVIOUS
    <2> QED BY <2>7, <2>8, <2>9, <2>10

  <1>5. CASE \E i \in Nodes : SendMsg(i)
    <2>pick. PICK i \in Nodes : SendMsg(i) BY <1>5
    <2> USE <2>pick DEF SendMsg
    <2>0. active[i] OBVIOUS
    <2>1. PICK j \in Nodes \ {i} :
            /\ active' = [active EXCEPT ![j] = TRUE]
            /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
      OBVIOUS
    <2>2. tpos' = tpos /\ tcolor' = tcolor
      OBVIOUS
    <2>3. j \in Nodes BY <2>1
    <2>4. active' \in [Nodes -> BOOLEAN]
      <3>1. active \in [Nodes -> BOOLEAN] OBVIOUS
      <3>2. TRUE \in BOOLEAN OBVIOUS
      <3> QED BY <3>1, <3>2, <2>1, <2>3
    <2>5. color' \in [Nodes -> Color]
      <3>1. color \in [Nodes -> Color] OBVIOUS
      <3>2. i \in Nodes OBVIOUS
      <3>3. "black" \in Color OBVIOUS
      <3>4. color[i] \in Color BY <3>1, <3>2
      <3>5. (IF j > i THEN "black" ELSE color[i]) \in Color BY <3>3, <3>4
      <3> QED BY <3>1, <3>2, <3>5, <2>1
    <2>6. tpos' \in Nodes BY <2>2
    <2>7. tcolor' \in Color BY <2>2
    <2>8. CASE \E k \in 0..tpos : color[k] = "black"
      <3>1. PICK k \in 0..tpos : color[k] = "black" BY <2>8
      <3>2. k \in 0..tpos' BY <2>2, <3>1
      <3>3. k \in Nodes BY <3>1
      <3>4. CASE k = i
        <4>1. color[i] = "black" BY <3>4, <3>1
        <4>2. color'[i] = IF j > i THEN "black" ELSE color[i] BY <2>1
        <4>3. color'[i] = "black" BY <4>1, <4>2
        <4>4. color'[k] = "black" BY <3>4, <4>3
        <4>5. \E m \in 0..tpos' : color'[m] = "black" BY <3>2, <4>4
        <4> QED BY <4>5, <2>4, <2>5, <2>6, <2>7
      <3>5. CASE k # i
        <4>1. color'[k] = color[k] BY <2>1, <3>5, <3>3
        <4>2. color'[k] = "black" BY <4>1, <3>1
        <4>3. \E m \in 0..tpos' : color'[m] = "black" BY <3>2, <4>2
        <4> QED BY <4>3, <2>4, <2>5, <2>6, <2>7
      <3> QED BY <3>4, <3>5
    <2>9. CASE tcolor = "black"
      <3>1. tcolor' = "black" BY <2>2, <2>9
      <3> QED BY <3>1, <2>4, <2>5, <2>6, <2>7
    <2>10. CASE \A k \in (tpos + 1)..(N-1) : ~active[k]
      <3>1. i \in 0..tpos
        <4>1. i \in 0..(N-1) OBVIOUS
        <4>2. ~(i \in (tpos+1)..(N-1)) BY <2>0, <2>10
        <4> QED BY <4>1, <4>2
      <3>2. CASE j > tpos
        <4>1. j > i
          <5>1. i <= tpos BY <3>1
          <5> QED BY <5>1, <3>2
        <4>2. color'[i] = "black"
          <5>1. color'[i] = IF j > i THEN "black" ELSE color[i] BY <2>1
          <5> QED BY <5>1, <4>1
        <4>3. i \in 0..tpos' BY <3>1, <2>2
        <4>4. \E m \in 0..tpos' : color'[m] = "black" BY <4>2, <4>3
        <4> QED BY <4>4, <2>4, <2>5, <2>6, <2>7
      <3>3. CASE ~(j > tpos)
        <4>1. j <= tpos BY <3>3
        <4>2. \A k \in (tpos' + 1)..(N-1) : ~active'[k]
          <5>1. TAKE k \in (tpos' + 1)..(N-1)
          <5>2. k \in (tpos + 1)..(N-1) BY <2>2
          <5>3. ~active[k] BY <5>2, <2>10
          <5>4. k # j
            <6>1. k > tpos BY <5>2
            <6> QED BY <6>1, <4>1
          <5>5. k \in Nodes BY <5>2
          <5>6. active'[k] = active[k] BY <2>1, <5>4, <5>5
          <5> QED BY <5>6, <5>3
        <4> QED BY <4>2, <2>4, <2>5, <2>6, <2>7
      <3> QED BY <3>2, <3>3
    <2>11. \/ \A k \in (tpos+1)..(N-1) : ~active[k]
           \/ \E k \in 0..tpos : color[k] = "black"
           \/ tcolor = "black"
      OBVIOUS
    <2> QED BY <2>8, <2>9, <2>10, <2>11

  <1>6. CASE \E i \in Nodes : Deactivate(i) \/ SendMsg(i)
    <2>1. PICK i \in Nodes : Deactivate(i) \/ SendMsg(i) BY <1>6
    <2>2. CASE Deactivate(i)
      <3> \E ii \in Nodes : Deactivate(ii) BY <2>1, <2>2
      <3> QED BY <1>4
    <2>3. CASE SendMsg(i)
      <3> \E ii \in Nodes : SendMsg(ii) BY <2>1, <2>3
      <3> QED BY <1>5
    <2> QED BY <2>1, <2>2, <2>3

  <1>7. QED BY <1>1, <1>2, <1>3, <1>6 DEF Next, Controlled, Environment

THEOREM Spec => []TerminationDetection
  <1>1. Init => IndInv BY InitInv
  <1>2. IndInv /\ [Next]_vars => IndInv' BY InvIsInductive
  <1>3. IndInv => TerminationDetection BY InvImpliesTermDet
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
