------------------------------ MODULE EuclidEx_PartialCorrectness ------------------------------
EXTENDS GCD, TLAPS
-----------------------------------------------------------------------------
CONSTANTS M, N
ASSUME MNPosInt == 
    /\ M \in Nat \ {0}
    /\ N \in Nat \ {0}
(*******************************************************************
--algorithm Euclid {
  variables x = M, y = N ;
  { while (x # y) { if (x < y) { y := y - x }
                    else       { x := x - y }
                  };
  }
}
 *******************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
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

Next == Lbl_1 \* Allow infinite stuttering to prevent deadlock on termination.
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (x = y) /\ (x = GCD(M, N))

TypeOK == 
    /\ x \in Nat \ {0}
    /\ y \in Nat \ {0}

Inv == 
    /\ TypeOK
    /\ GCD(x, y) = GCD(M, N)
    /\ (pc = "Done") => (x = y)
-----------------------------------------------------------------------------
LEMMA InitInv == Init => Inv
  BY MNPosInt DEF Init, Inv, TypeOK

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars
             PROVE Inv'
    OBVIOUS
<1>0. x \in Nat \ {0} /\ y \in Nat \ {0}
  BY DEF Inv, TypeOK
<1>1. CASE Lbl_1
  <2> USE <1>1 DEF Lbl_1
  <2>1. CASE x = y
    <3>1. pc' = "Done" /\ x' = x /\ y' = y
      BY <2>1
    <3> QED
      BY <3>1, <2>1, <1>0 DEF Inv, TypeOK
  <2>2. CASE x # y /\ x < y
    <3>1. x' = x /\ y' = y - x /\ pc' = "Lbl_1"
      BY <2>2
    <3>2. y - x \in Nat \ {0}
      BY <2>2, <1>0
    <3>3. GCD(x, y) = GCD(x, y - x)
      BY GCD3, <2>2, <1>0
    <3> QED
      BY <3>1, <3>2, <3>3, <1>0 DEF Inv, TypeOK
  <2>3. CASE x # y /\ ~(x < y)
    <3>0. x > y
      BY <2>3, <1>0
    <3>1. x' = x - y /\ y' = y /\ pc' = "Lbl_1"
      BY <2>3
    <3>2. x - y \in Nat \ {0}
      BY <3>0, <1>0
    <3>4a. GCD(x, y) = GCD(y, x)
      BY GCD2, <1>0
    <3>4b. GCD(y, x) = GCD(y, x - y)
      BY GCD3, <3>0, <1>0
    <3>4c. GCD(y, x - y) = GCD(x - y, y)
      BY GCD2, <3>2, <1>0
    <3> QED
      BY <3>1, <3>2, <3>4a, <3>4b, <3>4c, <1>0 DEF Inv, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3
<1>2. CASE UNCHANGED vars
  <2>1. x' = x /\ y' = y /\ pc' = pc
    BY <1>2 DEF vars
  <2> QED
    BY <2>1, <1>0 DEF Inv, TypeOK
<1> QED
  BY <1>1, <1>2 DEF Next

THEOREM InvHolds == Spec => []Inv
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY NextInv
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []PartialCorrectness
<1>1. Inv => PartialCorrectness
  <2> SUFFICES ASSUME Inv, pc = "Done"
               PROVE (x = y) /\ (x = GCD(M, N))
      BY DEF PartialCorrectness
  <2>1. x = y
    BY DEF Inv
  <2>2. x \in Nat \ {0}
    BY DEF Inv, TypeOK
  <2>3. GCD(x, y) = GCD(M, N)
    BY DEF Inv
  <2>4. GCD(x, x) = x
    BY GCD1, <2>2
  <2> QED
    BY <2>1, <2>3, <2>4
<1>2. Spec => []Inv
  BY InvHolds
<1> QED
  BY <1>1, <1>2, PTL
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 09:46:10 CST 2019 by hengxin
\* Created Mon Jul 15 16:59:12 CST 2019 by hengxin