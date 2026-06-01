------------------------------- MODULE Simple_AtLeastOneYWhenDone -------------------------------

EXTENDS Integers, TLAPS
------------------------------------------------------------------------------
CONSTANTS N 
------------------------------------------------------------------------------

------------------------------------------------------------------------------

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0 .. N-1)

Init == 
        /\ x = [i \in 0 .. N-1 |-> 0]
        /\ y = [i \in 0 .. N-1 |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

Proc(self) == s1(self) \/ s2(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0 .. N-1: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
AtLeastOneYWhenDone == (\A i \in 0 .. N-1 : pc[i] = "Done") => \E i \in 0 .. N-1 : y[i] = 1

------------------------------------------------------------------------------
ASSUME NIsInNat == N \in Nat \ {0}       

AXIOM ModInRange == \A i \in 0 .. N-1: (i-1) % N \in 0 .. N-1

THEOREM Spec => []AtLeastOneYWhenDone
PROOF OBVIOUS
=============================================================================

