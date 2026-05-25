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


THEOREM Spec => SV!Spec
PROOF OBVIOUS
=============================================================================
\* Modification History
\* Last modified Tue Aug 20 10:52:14 CST 2019 by hengxin
\* Created Thu Aug 15 10:52:49 CST 2019 by hengxin