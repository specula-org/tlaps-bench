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

TypeOK == /\ sum \in Nat
          /\ max \in Nat
          /\ i \in 0..N
          /\ pc \in {"Lbl_1", "Done"}

IndInv == /\ TypeOK
          /\ sum =< i * max
          /\ pc = "Done" => i = N

LEMMA InitIndInv == Init => IndInv
PROOF BY NType DEF Init, IndInv, TypeOK

LEMMA IndInvNext == IndInv /\ [Next]_vars => IndInv'
PROOF BY NType, aType, SMT DEF IndInv, TypeOK, Next, Lbl_1, vars

LEMMA IndInvCorrect == IndInv => Correctness
PROOF BY SMT DEF IndInv, TypeOK, Correctness

THEOREM Spec => []Correctness
PROOF
<1>1. Init => IndInv
  BY InitIndInv
<1>2. IndInv /\ [Next]_vars => IndInv'
  BY IndInvNext
<1>3. Spec => []IndInv
  BY <1>1, <1>2, PTL DEF Spec
<1>4. []IndInv => []Correctness
  BY IndInvCorrect, PTL
<1>5. QED
  BY <1>3, <1>4

=============================================================================

Writing algorithm and model checking: 15 min
Writing proof, before stopping to check for tlapm bug: 24 min
Writing proof: 12 min.
Writing proof: 12 min.
