------------------------------- MODULE EWD840_TerminationDetection -------------------------------
EXTENDS Naturals, TLAPS

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                    \* token position
  /\ tcolor \in Color                  \* token color

(* Initially the token is at node 0, and it is black. There
   are no constraints on the status and color of the nodes. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

(* Node 0 may initiate a probe when it has the token and when
   it is black or the token color is black. It passes
   a white token to node N-1 and paints itself white. *)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(* An inactive node different from 0 that possesses the token
   may pass it to node i-1 under the following circumstances:
   - node i is inactive or
   - node i is colored black or
   - the token is black.
   Note that the last two conditions will result in an
   inconclusive round, since the token will be black.
   The token will be stained if node i is black, otherwise 
   its color is unchanged. Node i will be made white. *)
PassToken(i) == 
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(* Any active node may become inactive at any moment. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(* Actions controlled by termination detection algorithm *)
Controlled ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)

(* Remaining actions, corresponding to environment transitions *)
Environment == \E i \in Nodes : Deactivate(i) \/ SendMsg(i)

Next == Controlled \/ Environment

vars == <<active, color, tpos, tcolor>>

Fairness == WF_vars(Controlled)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-invariants for validating the specification.                        *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(* This motivates weakening the fairness condition to WF_vars(Controlled). *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's invariant                                                    *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

-----------------------------------------------------------------------------

(* TypeOK is an inductive invariant *)

(***************************************************************************)
(* The combined inductive invariant: type-correctness together with        *)
(* Dijkstra's invariant.                                                   *)
(***************************************************************************)
IndInv == TypeOK /\ Inv

LEMMA InitIndInv == Init => IndInv
  BY NAssumption DEF Init, IndInv, TypeOK, Inv, Nodes, Color

LEMMA NextIndInv == IndInv /\ [Next]_vars => IndInv'
<1> SUFFICES ASSUME IndInv, [Next]_vars
             PROVE  IndInv'
  OBVIOUS
<1> USE NAssumption DEF IndInv, TypeOK, Inv, Nodes, Color
<1>1. CASE InitiateProbe
  <2> USE <1>1 DEF InitiateProbe
  <2>1. TypeOK'
    BY DEF TypeOK
  <2>2. \A k \in Nodes : tpos' < k => ~ active'[k]
    OBVIOUS
  <2>3. Inv'
    BY <2>2 DEF Inv
  <2>4. QED
    BY <2>1, <2>3 DEF IndInv
<1>2. ASSUME NEW i \in Nodes \ {0}, PassToken(i)
      PROVE  IndInv'
  <2> USE <1>2 DEF PassToken
  <2>1. TypeOK'
    BY DEF TypeOK, Color
  <2>2. Inv'
    <3>1. CASE color[i] = "black"
      BY <3>1 DEF Inv
    <3>2. CASE color[i] # "black" /\ tcolor = "black"
      BY <3>2 DEF Inv
    <3>3. CASE color[i] # "black" /\ tcolor # "black"
      <4>1. ~ active[i]
        BY <3>3
      <4>2. (\A k \in Nodes : tpos < k => ~ active[k]) \/ (\E k \in 0..tpos : color[k] = "black")
        BY <3>3 DEF Inv
      <4>3. CASE \A k \in Nodes : tpos < k => ~ active[k]
        <5>1. \A k \in Nodes : tpos' < k => ~ active'[k]
          BY <4>1, <4>3
        <5>2. QED
          BY <5>1 DEF Inv
      <4>4. CASE \E k \in 0..tpos : color[k] = "black"
        <5>1. PICK k \in 0..tpos : color[k] = "black"
          BY <4>4
        <5>2. k \in Nodes
          BY <5>1 DEF TypeOK
        <5>3. k # i
          BY <5>1, <3>3
        <5>4. k \in 0..tpos'
          BY <5>1, <5>3
        <5>5. color'[k] = "black"
          BY <5>1, <5>2, <5>3
        <5>6. QED
          BY <5>4, <5>5 DEF Inv
      <4>5. QED
        BY <4>2, <4>3, <4>4
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>3. QED
    BY <2>1, <2>2 DEF IndInv
<1>3. ASSUME NEW i \in Nodes, Deactivate(i) \/ SendMsg(i)
      PROVE  IndInv'
  <2> USE <1>3
  <2>1. CASE Deactivate(i)
    <3> USE <2>1 DEF Deactivate
    <3>1. TypeOK'
      BY DEF TypeOK
    <3>2. Inv'
      <4>1. CASE \A k \in Nodes : tpos < k => ~ active[k]
        <5>1. \A k \in Nodes : tpos' < k => ~ active'[k]
          BY <4>1
        <5>2. QED
          BY <5>1 DEF Inv
      <4>2. CASE \E k \in 0..tpos : color[k] = "black"
        BY <4>2 DEF Inv
      <4>3. CASE tcolor = "black"
        BY <4>3 DEF Inv
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv
    <3>3. QED
      BY <3>1, <3>2 DEF IndInv
  <2>2. CASE SendMsg(i)
    <3> USE <2>2 DEF SendMsg
    <3>1. PICK j \in Nodes \ {i} :
            /\ active' = [active EXCEPT ![j] = TRUE]
            /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE color[i]]
      BY DEF SendMsg
    <3>2. TypeOK'
      BY <3>1 DEF TypeOK, Color
    <3>3. Inv'
      <4>1. CASE tcolor = "black"
        BY <4>1 DEF Inv
      <4>2. CASE \E k \in 0..tpos : color[k] = "black"
        <5>1. PICK k \in 0..tpos : color[k] = "black"
          BY <4>2
        <5>2. k \in Nodes
          BY <5>1 DEF TypeOK
        <5>3. color'[k] = "black"
          BY <5>1, <5>2, <3>1
        <5>4. k \in 0..tpos'
          BY <5>1
        <5>5. QED
          BY <5>3, <5>4 DEF Inv
      <4>3. CASE \A k \in Nodes : tpos < k => ~ active[k]
        <5>1. CASE j <= tpos
          <6>1. \A k \in Nodes : tpos' < k => ~ active'[k]
            BY <4>3, <5>1, <3>1
          <6>2. QED
            BY <6>1 DEF Inv
        <5>2. CASE ~ (j <= tpos)
          <6>1. active[i]
            BY DEF SendMsg
          <6>2. ~ (tpos < i)
            BY <4>3, <6>1
          <6>3. i <= tpos
            BY <6>2
          <6>4. j > i
            BY <5>2, <6>3
          <6>5. color'[i] = "black"
            BY <3>1, <6>4
          <6>6. i \in 0..tpos'
            BY <6>3
          <6>7. QED
            BY <6>5, <6>6 DEF Inv
        <5>3. QED
          BY <5>1, <5>2
      <4>4. QED
        BY <4>1, <4>2, <4>3 DEF Inv
    <3>4. QED
      BY <3>2, <3>3 DEF IndInv
  <2>3. QED
    BY <2>1, <2>2
<1>4. CASE vars' = vars
  BY <1>4 DEF vars, IndInv, TypeOK, Inv
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next, Controlled, Environment

LEMMA TypeAndInvariant == Spec => []IndInv
<1>1. Init => IndInv
  BY InitIndInv
<1>2. IndInv /\ [Next]_vars => IndInv'
  BY NextIndInv
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

LEMMA IndInvImpliesTD == IndInv => TerminationDetection
<1> SUFFICES ASSUME IndInv, terminationDetected
             PROVE  \A i \in Nodes : ~ active[i]
  BY DEF TerminationDetection
<1> USE DEF IndInv, TypeOK, Inv, terminationDetected, Nodes, Color
<1>1. tcolor # "black"
  OBVIOUS
<1>2. ~ (\E k \in 0..tpos : color[k] = "black")
  OBVIOUS
<1>3. \A k \in Nodes : tpos < k => ~ active[k]
  BY <1>1, <1>2 DEF Inv
<1>4. QED
  BY <1>3


THEOREM Spec => []TerminationDetection
<1>1. Spec => []IndInv
  BY TypeAndInvariant
<1>2. IndInv => TerminationDetection
  BY IndInvImpliesTD
<1>3. QED
  BY <1>1, <1>2, PTL


=============================================================================
\* Modification History
\* Last modified Wed Aug 06 12:26:15 CEST 2014 by merz
\* Last modified Fri May 30 23:04:12 CEST 2014 by shaolin
\* Last modified Wed May 21 11:36:56 CEST 2014 by jael
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
