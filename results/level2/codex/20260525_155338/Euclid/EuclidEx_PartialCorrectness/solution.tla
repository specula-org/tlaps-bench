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
PosNat == Nat \ {0}

TypeOK ==
    /\ x \in PosNat
    /\ y \in PosNat
    /\ pc \in {"Lbl_1", "Done"}

GCDInv == GCD(x, y) = GCD(M, N)

IndInv ==
    /\ TypeOK
    /\ GCDInv
    /\ (pc = "Done" => x = y)

LEMMA PosNatSub ==
    \A a, b \in PosNat : a < b => b - a \in PosNat
PROOF BY SMT DEF PosNat

LEMMA GCDReduceRight ==
    \A a, b \in PosNat : a < b => GCD(a, b - a) = GCD(a, b)
PROOF BY GCD3 DEF PosNat

LEMMA GCDReduceLeft ==
    \A a, b \in PosNat : b < a => GCD(a - b, b) = GCD(a, b)
PROOF BY GCD2, GCD3 DEF PosNat

LEMMA InitIndInv == Init => IndInv
PROOF BY MNPosInt, GCD1, SMT DEF Init, IndInv, TypeOK, GCDInv, PosNat

LEMMA NextIndInv == IndInv /\ [Next]_vars => IndInv'
PROOF BY PosNatSub, GCDReduceRight, GCDReduceLeft, SMT
         DEF IndInv, TypeOK, GCDInv, Next, Lbl_1, vars, PosNat

LEMMA IndInvPartialCorrectness == IndInv => PartialCorrectness
PROOF
    <1>1. ASSUME IndInv, pc = "Done"
          PROVE  x = y /\ x = GCD(M, N)
        PROOF
            <2>1. x \in PosNat /\ y \in PosNat /\ GCD(x, y) = GCD(M, N)
                BY <1>1 DEF IndInv, TypeOK, GCDInv
            <2>2. x = y
                BY <1>1 DEF IndInv
            <2>3. GCD(x, x) = x
                BY <2>1, GCD1 DEF PosNat
            <2>4. x = GCD(M, N)
                BY <2>1, <2>2, <2>3, SMT
            <2> QED
                BY <2>2, <2>4
    <1>2. QED
        BY <1>1 DEF PartialCorrectness

THEOREM Spec => []PartialCorrectness
PROOF
    <1>1. Spec => []IndInv
        BY InitIndInv, NextIndInv, PTL DEF Spec
    <1>2. []IndInv => []PartialCorrectness
        BY IndInvPartialCorrectness, PTL
    <1>3. QED
        BY <1>1, <1>2, PTL
=============================================================================
