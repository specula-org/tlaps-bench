--------------------------- MODULE GCD_GCD3 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------

LEMMA DistribSub ==
  \A p, q1, q2, m, n \in Int :
    (m = p * q1 /\ n = p * q2) => (n - m = p * (q2 - q1))
OBVIOUS

LEMMA DistribAdd ==
  \A p, q1, q2, m, n \in Int :
    (m = p * q1 /\ (n - m) = p * q2) => (n = p * (q1 + q2))
OBVIOUS

LEMMA DivisorsEqual ==
  \A m, n \in Int :
    DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n - m)
<1> TAKE m, n \in Int
<1>1. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n)
      PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n - m)
  <2>1. p \in Int
        BY <1>1 DEF DivisorsOf
  <2>2. p \in DivisorsOf(m)
        BY <1>1
  <2>3. Divides(p, m)
        BY <1>1 DEF DivisorsOf
  <2>4. Divides(p, n)
        BY <1>1 DEF DivisorsOf
  <2>5. PICK q1 \in Int : m = p * q1
        BY <2>3 DEF Divides
  <2>6. PICK q2 \in Int : n = p * q2
        BY <2>4 DEF Divides
  <2>7. q2 - q1 \in Int
        OBVIOUS
  <2>8. n - m = p * (q2 - q1)
        BY <2>1, <2>5, <2>6, DistribSub
  <2>9. Divides(p, n - m)
        BY <2>7, <2>8 DEF Divides
  <2>10. p \in DivisorsOf(n - m)
        BY <2>1, <2>9 DEF DivisorsOf
  <2> QED BY <2>2, <2>10
<1>2. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n - m)
      PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n)
  <2>1. p \in Int
        BY <1>2 DEF DivisorsOf
  <2>2. p \in DivisorsOf(m)
        BY <1>2
  <2>3. Divides(p, m)
        BY <1>2 DEF DivisorsOf
  <2>4. Divides(p, n - m)
        BY <1>2 DEF DivisorsOf
  <2>5. PICK q1 \in Int : m = p * q1
        BY <2>3 DEF Divides
  <2>6. PICK q2 \in Int : (n - m) = p * q2
        BY <2>4 DEF Divides
  <2>7. q1 + q2 \in Int
        OBVIOUS
  <2>8. n = p * (q1 + q2)
        BY <2>1, <2>5, <2>6, DistribAdd
  <2>9. Divides(p, n)
        BY <2>7, <2>8 DEF Divides
  <2>10. p \in DivisorsOf(n)
        BY <2>1, <2>9 DEF DivisorsOf
  <2> QED BY <2>2, <2>10
<1> QED BY <1>1, <1>2

------------------------------------------------------------------
------------------------------------------------------------------
THEOREM GCD3 == \A m, n \in Nat \ {0} :
                    (n > m) => (GCD(m, n) = GCD(m, n-m))
<1> TAKE m, n \in Nat \ {0}
<1> HAVE n > m
<1>1. m \in Int /\ n \in Int
      OBVIOUS
<1>2. DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n - m)
      BY <1>1, DivisorsEqual
<1> QED BY <1>2 DEF GCD
===================================================================
