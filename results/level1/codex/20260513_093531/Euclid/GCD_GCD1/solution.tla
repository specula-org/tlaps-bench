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
  <1>1. SUFFICES ASSUME NEW m \in Nat \ {0}
                 PROVE  GCD(m, m) = m
    OBVIOUS
  <1>2. m \in DivisorsOf(m) \cap DivisorsOf(m)
    BY <1>1 DEF DivisorsOf, Divides
  <1>3. \A p \in DivisorsOf(m) \cap DivisorsOf(m) : m >= p
    BY <1>1 DEF DivisorsOf, Divides
  <1>4. \A i \in DivisorsOf(m) \cap DivisorsOf(m) :
          (\A j \in DivisorsOf(m) \cap DivisorsOf(m) : i >= j) => i = m
    PROOF
      <2>1. TAKE i \in DivisorsOf(m) \cap DivisorsOf(m)
      <2>2. SUFFICES ASSUME \A j \in DivisorsOf(m) \cap DivisorsOf(m) : i >= j
                     PROVE  i = m
        OBVIOUS
      <2>3. i >= m
        BY <1>2, <2>2
      <2>4. m >= i
        BY <1>3, <2>1
      <2>5. i \in Int
        BY <2>1 DEF DivisorsOf
      <2>6. QED
        BY <1>1, <2>3, <2>4, <2>5
  <1>5. GCD(m, m) = m
    BY <1>2, <1>3, <1>4 DEF GCD, SetMax
  <1>6. QED
    BY <1>5

===================================================================
