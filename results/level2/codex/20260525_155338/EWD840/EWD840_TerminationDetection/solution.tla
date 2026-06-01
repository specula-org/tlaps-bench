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

DirtyInv ==
  \A i \in Nodes :
    active[i] /\ tpos < i =>
      tcolor = "black" \/ \E j \in 0..tpos : color[j] = "black"

IndInv == TypeOK /\ DirtyInv

LEMMA InitIndInv == Init => IndInv
PROOF
  BY NAssumption DEF Init, IndInv, TypeOK, DirtyInv, Nodes, Color

LEMMA InitiateProbeIndInv == IndInv /\ InitiateProbe => IndInv'
PROOF
  BY NAssumption DEF IndInv, TypeOK, DirtyInv, InitiateProbe, Nodes, Color

LEMMA PassTokenIndInv ==
  \A i \in Nodes \ {0} : IndInv /\ PassToken(i) => IndInv'
PROOF
  BY NAssumption DEF IndInv, TypeOK, DirtyInv, PassToken, Nodes, Color

LEMMA SendMsgIndInv ==
  \A i \in Nodes : IndInv /\ SendMsg(i) => IndInv'
PROOF
  BY NAssumption DEF IndInv, TypeOK, DirtyInv, SendMsg, Nodes, Color

LEMMA DeactivateIndInv ==
  \A i \in Nodes : IndInv /\ Deactivate(i) => IndInv'
PROOF
  BY NAssumption DEF IndInv, TypeOK, DirtyInv, Deactivate, Nodes, Color

LEMMA UnchangedIndInv == IndInv /\ UNCHANGED vars => IndInv'
PROOF
  BY DEF IndInv, TypeOK, DirtyInv, vars

LEMMA NextIndInv == IndInv /\ [Next]_vars => IndInv'
PROOF
  BY InitiateProbeIndInv, PassTokenIndInv, SendMsgIndInv, DeactivateIndInv
     , UnchangedIndInv
     DEF IndInv, Next, Controlled, Environment, vars

LEMMA IndInvImpliesTerminationDetection == IndInv => TerminationDetection
PROOF
  BY DEF IndInv, TypeOK, DirtyInv, TerminationDetection,
         terminationDetected, Nodes

THEOREM Spec => []TerminationDetection
PROOF
  <1>1. Spec => []IndInv
    BY InitIndInv, NextIndInv, PTL DEF Spec
  <1>2. IndInv => TerminationDetection
    BY IndInvImpliesTerminationDetection
  <1>3. []IndInv => []TerminationDetection
    BY <1>2, PTL
  <1>4. QED
    BY <1>1, <1>3, PTL

=============================================================================
