--------------------------- MODULE GCD_GCD1 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF
  <1>0. SUFFICES ASSUME NEW m \in Nat \ {0}
        PROVE GCD(m, m) = m
    OBVIOUS
  <1>1. m \in DivisorsOf(m) \cap DivisorsOf(m)
    BY DEF DivisorsOf, Divides
  <1>2. \A j \in DivisorsOf(m) \cap DivisorsOf(m) : m >= j
    BY DEF DivisorsOf, Divides
  <1>3. GCD(m, m) = m
    BY <1>1, <1>2 DEF GCD, SetMax
  <1>4. QED
    BY <1>3

===================================================================
