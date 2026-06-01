------------------------------ MODULE EuclidEx_PartialCorrectness ------------------------------
EXTENDS GCD, TLAPS
-----------------------------------------------------------------------------
CONSTANTS M, N
ASSUME MNPosInt ==
    /\ M \in Nat \ {0}
    /\ N \in Nat \ {0}

VARIABLES x, y, pc

vars == << x, y, pc >>

Init ==
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

Next == Lbl_1
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (x = y) /\ (x = GCD(M, N))

-----------------------------------------------------------------------------
IndInv ==
    /\ pc \in {"Lbl_1", "Done"}
    /\ x \in Nat \ {0}
    /\ y \in Nat \ {0}
    /\ GCD(x, y) = GCD(M, N)
    /\ (pc = "Done") => (x = y)

LEMMA InitInv == Init => IndInv
  BY MNPosInt DEF Init, IndInv

LEMMA NextInv == IndInv /\ [Next]_vars => IndInv'
  <1> SUFFICES ASSUME IndInv, [Next]_vars
                PROVE IndInv'
      OBVIOUS
  <1>1. CASE Lbl_1
    <2>1. pc = "Lbl_1" BY <1>1 DEF Lbl_1
    <2>2. x \in Nat \ {0} BY DEF IndInv
    <2>3. y \in Nat \ {0} BY DEF IndInv
    <2>4. GCD(x, y) = GCD(M, N) BY DEF IndInv
    <2>5. CASE x # y
      <3>1. CASE x < y
        <4>1. y' = y - x BY <1>1, <2>5, <3>1 DEF Lbl_1
        <4>2. x' = x BY <1>1, <2>5, <3>1 DEF Lbl_1
        <4>3. pc' = "Lbl_1" BY <1>1, <2>5 DEF Lbl_1
        <4>4. y > x BY <3>1, <2>2, <2>3
        <4>5. y - x \in Nat \ {0} BY <2>2, <2>3, <4>4
        <4>6. GCD(x, y) = GCD(x, y - x) BY <2>2, <2>3, <4>4, GCD3
        <4>7. GCD(x', y') = GCD(M, N) BY <4>1, <4>2, <4>6, <2>4
        <4>8. x' \in Nat \ {0} BY <4>2, <2>2
        <4>9. y' \in Nat \ {0} BY <4>1, <4>5
        <4>10. pc' \in {"Lbl_1", "Done"} BY <4>3
        <4>11. (pc' = "Done") => (x' = y') BY <4>3
        <4>12. QED BY <4>7, <4>8, <4>9, <4>10, <4>11 DEF IndInv
      <3>2. CASE ~(x < y)
        <4>1. x' = x - y BY <1>1, <2>5, <3>2 DEF Lbl_1
        <4>2. y' = y BY <1>1, <2>5, <3>2 DEF Lbl_1
        <4>3. pc' = "Lbl_1" BY <1>1, <2>5 DEF Lbl_1
        <4>4. x > y BY <2>5, <3>2, <2>2, <2>3
        <4>5. x - y \in Nat \ {0} BY <2>2, <2>3, <4>4
        <4>6. GCD(y, x) = GCD(y, x - y) BY <2>2, <2>3, <4>4, GCD3
        <4>7. GCD(x, y) = GCD(y, x) BY <2>2, <2>3, GCD2
        <4>8. GCD(x - y, y) = GCD(y, x - y) BY <2>3, <4>5, GCD2
        <4>9. GCD(x', y') = GCD(M, N) BY <4>1, <4>2, <4>6, <4>7, <4>8, <2>4
        <4>10. x' \in Nat \ {0} BY <4>1, <4>5
        <4>11. y' \in Nat \ {0} BY <4>2, <2>3
        <4>12. pc' \in {"Lbl_1", "Done"} BY <4>3
        <4>13. (pc' = "Done") => (x' = y') BY <4>3
        <4>14. QED BY <4>9, <4>10, <4>11, <4>12, <4>13 DEF IndInv
      <3>3. QED BY <3>1, <3>2
    <2>6. CASE x = y
      <3>1. pc' = "Done" BY <1>1, <2>6 DEF Lbl_1
      <3>2. x' = x /\ y' = y BY <1>1, <2>6 DEF Lbl_1
      <3>3. GCD(x', y') = GCD(M, N) BY <3>2, <2>4
      <3>4. x' \in Nat \ {0} BY <3>2, <2>2
      <3>5. y' \in Nat \ {0} BY <3>2, <2>3
      <3>6. pc' \in {"Lbl_1", "Done"} BY <3>1
      <3>7. (pc' = "Done") => (x' = y') BY <3>2, <2>6
      <3>8. QED BY <3>3, <3>4, <3>5, <3>6, <3>7 DEF IndInv
    <2>7. QED BY <2>5, <2>6
  <1>2. CASE pc = "Done" /\ UNCHANGED vars
    <2>1. x' = x /\ y' = y /\ pc' = pc BY <1>2 DEF vars
    <2>2. QED BY <2>1 DEF IndInv
  <1>3. CASE UNCHANGED vars
    <2>1. x' = x /\ y' = y /\ pc' = pc BY <1>3 DEF vars
    <2>2. QED BY <2>1 DEF IndInv
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Next

LEMMA InvImpPC == IndInv => PartialCorrectness
  <1> SUFFICES ASSUME IndInv PROVE PartialCorrectness
      OBVIOUS
  <1>1. CASE pc = "Done"
    <2>1. x = y BY <1>1 DEF IndInv
    <2>2. GCD(x, y) = GCD(M, N) BY DEF IndInv
    <2>3. x \in Nat \ {0} BY DEF IndInv
    <2>4. GCD(x, x) = x BY <2>3, GCD1
    <2>5. x = GCD(M, N) BY <2>1, <2>2, <2>4
    <2>6. QED BY <1>1, <2>1, <2>5 DEF PartialCorrectness
  <1>2. CASE pc # "Done"
    <2>1. QED BY <1>2 DEF PartialCorrectness
  <1>3. QED BY <1>1, <1>2

THEOREM Spec => []PartialCorrectness
  <1>1. Init => IndInv BY InitInv
  <1>2. IndInv /\ [Next]_vars => IndInv' BY NextInv
  <1>3. IndInv => PartialCorrectness BY InvImpPC
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
