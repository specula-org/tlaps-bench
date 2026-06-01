--------------------------- MODULE GCD_GCD2 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
LEMMA IntersectCommutative == \A S, T : S \cap T = T \cap S
PROOF
  <1>1. \A S, T : \A x : x \in S \cap T <=> x \in T \cap S
    OBVIOUS
  <1>2. QED
    BY <1>1

------------------------------------------------------------------
THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
PROOF
  <1>1. \A m, n \in Nat \ {0} :
          DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(n) \cap DivisorsOf(m)
    BY IntersectCommutative
  <1>2. QED
    BY <1>1 DEF GCD
------------------------------------------------------------------
===================================================================
