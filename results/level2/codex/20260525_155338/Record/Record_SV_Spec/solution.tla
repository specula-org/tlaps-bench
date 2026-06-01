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

IndInv == state \in [Participant -> [Participant -> [maxBal : Nat, maxVBal : Nat]]]

LEMMA IndInvInit ==
    Init => IndInv
PROOF BY SMT DEF Init, IndInv, InitState

LEMMA IndInvPrepare ==
    \A p \in Participant, b \in Nat :
        IndInv /\ Prepare(p, b) => IndInv'
PROOF BY SMT DEF IndInv, Prepare

LEMMA IndInvNext ==
    IndInv /\ Next => IndInv'
PROOF BY IndInvPrepare DEF Next

LEMMA IndInvStutter ==
    IndInv /\ UNCHANGED state => IndInv'
PROOF BY SMT DEF IndInv

LEMMA IndInvAction ==
    IndInv /\ [Next]_state => IndInv'
PROOF BY IndInvNext, IndInvStutter

LEMMA IndInvSpec ==
    Spec => []IndInv
PROOF BY IndInvInit, IndInvAction, PTL DEF Spec

LEMMA InitRef ==
    Init => SV!Init
PROOF BY SMT DEF Init, SV!Init, maxBal, InitState

LEMMA MaxBalExcept ==
    IndInv => \A p \in Participant, b \in Nat :
        [q \in Participant |-> [state EXCEPT ![p][p].maxBal = b][q][q].maxBal]
        = [[q \in Participant |-> state[q][q].maxBal] EXCEPT ![p] = b]
PROOF
<1>. SUFFICES ASSUME IndInv, NEW p \in Participant, NEW b \in Nat
              PROVE  [q \in Participant |-> [state EXCEPT ![p][p].maxBal = b][q][q].maxBal]
                     = [[q \in Participant |-> state[q][q].maxBal] EXCEPT ![p] = b]
  OBVIOUS
<1>1. \A q \in Participant :
        [r \in Participant |-> [state EXCEPT ![p][p].maxBal = b][r][r].maxBal][q]
        = [[r \in Participant |-> state[r][r].maxBal] EXCEPT ![p] = b][q]
  PROOF
  <2>. SUFFICES ASSUME NEW q \in Participant
                PROVE  [r \in Participant |-> [state EXCEPT ![p][p].maxBal = b][r][r].maxBal][q]
                       = [[r \in Participant |-> state[r][r].maxBal] EXCEPT ![p] = b][q]
    OBVIOUS
  <2>1. CASE q = p
    <3>1. [r \in Participant |-> [state EXCEPT ![p][p].maxBal = b][r][r].maxBal][q]
           = [state EXCEPT ![p][p].maxBal = b][p][p].maxBal
      BY <2>1, SMT
    <3>2. [state EXCEPT ![p][p].maxBal = b][p][p].maxBal = b
      BY <2>1, SMT DEF IndInv
    <3>3. [[r \in Participant |-> state[r][r].maxBal] EXCEPT ![p] = b][q] = b
      BY <2>1, SMT
    <3>. QED BY <3>1, <3>2, <3>3
  <2>2. CASE q # p
    BY <2>2, SimplifyAndSolve DEF IndInv
  <2>. QED BY <2>1, <2>2
<1>. QED BY <1>1, SMT

LEMMA PrepareRef ==
    \A p \in Participant, b \in Nat :
        IndInv /\ Prepare(p, b) => SV!IncreaseMaxBal(p, b)
PROOF BY MaxBalExcept, SMT DEF Prepare, SV!IncreaseMaxBal, maxBal

LEMMA NextRef ==
    IndInv /\ Next => SV!Next
PROOF BY PrepareRef DEF Next, SV!Next

LEMMA StutterRef ==
    UNCHANGED state => UNCHANGED maxBal
PROOF BY SMT DEF maxBal

LEMMA ActionRef ==
    IndInv /\ [Next]_state => [SV!Next]_maxBal
PROOF BY NextRef, StutterRef

THEOREM Spec => SV!Spec
PROOF BY InitRef, IndInvSpec, ActionRef, PTL DEF Spec, SV!Spec
=============================================================================
