--------------------------- MODULE GCD_GCD3 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
------------------------------------------------------------------
LEMMA DistribMinus == \A p, x, y \in Int : p * (x - y) = p * x - p * y
  OBVIOUS

LEMMA DistribPlus == \A p, x, y \in Int : p * (x + y) = p * x + p * y
  OBVIOUS

------------------------------------------------------------------
LEMMA DivisorsEqual ==
  \A m, n \in Int :
    DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n - m)
PROOF
<1> TAKE m, n \in Int
<1>1. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n)
      PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n - m)
  <2>1. p \in Int /\ Divides(p, m) /\ Divides(p, n)
    BY <1>1 DEF DivisorsOf
  <2>2. PICK a \in Int : m = p * a  BY <2>1 DEF Divides
  <2>3. PICK b \in Int : n = p * b  BY <2>1 DEF Divides
  <2>4. n - m = p * (b - a)
    BY <2>1, <2>2, <2>3, DistribMinus
  <2>5. Divides(p, n - m)
    BY <2>4 DEF Divides
  <2>6. QED
    BY <2>1, <2>5 DEF DivisorsOf
<1>2. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n - m)
      PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n)
  <2>1. p \in Int /\ Divides(p, m) /\ Divides(p, n - m)
    BY <1>2 DEF DivisorsOf
  <2>2. PICK a \in Int : m = p * a  BY <2>1 DEF Divides
  <2>3. PICK c \in Int : n - m = p * c  BY <2>1 DEF Divides
  <2>4. n = p * (c + a)
    BY <2>1, <2>2, <2>3, DistribPlus
  <2>5. Divides(p, n)
    BY <2>4 DEF Divides
  <2>6. QED
    BY <2>1, <2>5 DEF DivisorsOf
<1>3. QED
  BY <1>1, <1>2

------------------------------------------------------------------
------------------------------------------------------------------
THEOREM GCD3 == \A m, n \in Nat \ {0} :
                    (n > m) => (GCD(m, n) = GCD(m, n-m))
PROOF
<1> SUFFICES ASSUME NEW m \in Nat \ {0}, NEW n \in Nat \ {0}, n > m
             PROVE  GCD(m, n) = GCD(m, n - m)
  OBVIOUS
<1>1. m \in Int /\ n \in Int
  OBVIOUS
<1>2. DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n - m)
  BY <1>1, DivisorsEqual
<1>3. QED
  BY <1>2 DEF GCD
===================================================================