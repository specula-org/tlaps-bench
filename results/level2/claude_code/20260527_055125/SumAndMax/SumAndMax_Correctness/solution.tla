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

IndInv ==
    /\ sum \in Nat
    /\ max \in Nat
    /\ i \in 0..N
    /\ pc \in {"Lbl_1", "Done"}
    /\ (pc = "Done" => i = N)
    /\ (\A j \in 0..(i-1) : a[j] =< max)
    /\ sum =< i * max

LEMMA MulMono ==
    ASSUME NEW k \in Nat, NEW m1 \in Nat, NEW m2 \in Nat, m1 =< m2
    PROVE k * m1 =< k * m2
  BY Z3

LEMMA Distrib ==
    ASSUME NEW k \in Nat, NEW m \in Nat
    PROVE (k+1) * m = k * m + m
  BY Z3

LEMMA InitInv == Init => IndInv
  <1> SUFFICES ASSUME Init PROVE IndInv
      OBVIOUS
  <1> USE NType DEF Init, IndInv
  <1>1. sum \in Nat OBVIOUS
  <1>2. max \in Nat OBVIOUS
  <1>3. i \in 0..N OBVIOUS
  <1>4. pc \in {"Lbl_1", "Done"} OBVIOUS
  <1>5. pc = "Done" => i = N OBVIOUS
  <1>6. \A j \in 0..(i-1) : a[j] =< max
    <2>1. 0..(i-1) = {} OBVIOUS
    <2> QED BY <2>1
  <1>7. sum =< i * max OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

LEMMA NextInv == IndInv /\ [Next]_vars => IndInv'
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
      OBVIOUS
  <1>1. CASE Lbl_1
    <2>1. CASE i < N
      <3> USE NType, aType, <1>1, <2>1 DEF Lbl_1, IndInv
      <3>a. i \in 0..(N-1) OBVIOUS
      <3>b. i \in DOMAIN a BY <3>a
      <3>c. a[i] \in Nat BY <3>b
      <3>d. sum' = sum + a[i] OBVIOUS
      <3>e. i' = i + 1 OBVIOUS
      <3>f. pc' = "Lbl_1" OBVIOUS
      <3>g. max' = (IF max < a[i] THEN a[i] ELSE max) OBVIOUS
      <3>h. max' \in Nat BY <3>g, <3>c
      <3>i. max =< max' BY <3>g
      <3>j. a[i] =< max' BY <3>g, <3>c
      <3>1. sum' \in Nat BY <3>d, <3>c
      <3>2. max' \in Nat BY <3>h
      <3>3. i' \in 0..N BY <3>e
      <3>4. pc' \in {"Lbl_1", "Done"} BY <3>f
      <3>5. pc' = "Done" => i' = N BY <3>f
      <3>6. \A j \in 0..(i'-1) : a[j] =< max'
        <4>1. 0..(i'-1) = (0..(i-1)) \cup {i} BY <3>e
        <4>2. \A j \in 0..(i-1) : a[j] =< max' BY <3>i
        <4>3. a[i] =< max' BY <3>j
        <4> QED BY <4>1, <4>2, <4>3
      <3>7. sum' =< i' * max'
        <4>1. sum =< i * max OBVIOUS
        <4>2. i \in Nat OBVIOUS
        <4>3. i * max =< i * max' BY MulMono, <4>2, <3>i, <3>h
        <4>4. sum =< i * max' BY <4>1, <4>3
        <4>5. sum + a[i] =< i * max' + max' BY <4>4, <3>j, <3>c, <3>h
        <4>6. (i+1) * max' = i * max' + max' BY Distrib, <4>2, <3>h
        <4>7. i' * max' = (i+1) * max' BY <3>e
        <4> QED BY <4>5, <4>6, <4>7, <3>d
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF IndInv
    <2>2. CASE ~(i < N)
      <3> USE NType, aType, <1>1, <2>2 DEF Lbl_1, IndInv
      <3>1. i = N OBVIOUS
      <3>2. sum' = sum /\ max' = max /\ i' = i OBVIOUS
      <3>3. pc' = "Done" OBVIOUS
      <3> QED BY <3>1, <3>2, <3>3 DEF IndInv
    <2> QED BY <2>1, <2>2
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF vars, IndInv
  <1> QED BY <1>1, <1>2 DEF Next

LEMMA InvCorrect == IndInv => Correctness
  <1> SUFFICES ASSUME IndInv, pc = "Done" PROVE sum =< N * max
      BY DEF Correctness
  <1> USE NType DEF IndInv
  <1>1. i = N OBVIOUS
  <1>2. sum =< i * max OBVIOUS
  <1> QED BY <1>1, <1>2

THEOREM Spec => []Correctness
  <1>1. Init => IndInv BY InitInv
  <1>2. IndInv /\ [Next]_vars => IndInv' BY NextInv
  <1>3. IndInv => Correctness BY InvCorrect
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================

Writing algorithm and model checking: 15 min
Writing proof, before stopping to check for tlapm bug: 24 min
Writing proof: 12 min.
Writing proof: 12 min.
