----------------------------- MODULE SumAndMax_Correctness -----------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NType == N \in Nat
CONSTANT a
ASSUME aType == a \in [0..(N-1) -> Nat]

VARIABLES sum, max, i, pc

vars == << sum, max, i, pc >>

Init == 
        /\ sum = 0
        /\ max = 0
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < N
               THEN /\ IF max < a[i]
                          THEN /\ max' = a[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ sum' = sum + a[i]
                    /\ i' = i+1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << sum, max, i >>

Next == Lbl_1
           \/ 
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correctness == pc = "Done" => sum =< N*max

THEOREM Spec => []Correctness
PROOF OBVIOUS

=============================================================================

Writing algorithm and model checking: 15 min
Writing proof, before stopping to check for tlapm bug: 24 min
Writing proof: 12 min.
Writing proof: 12 min.
