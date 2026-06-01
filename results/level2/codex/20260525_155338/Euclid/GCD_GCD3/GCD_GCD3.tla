--------------------------- MODULE GCD_GCD3 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
LOCAL INSTANCE TLAPS
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
------------------------------------------------------------------
LEMMA CommonDivisorSubtract ==
  \A p, m, n \in Int :
    (Divides(p, m) /\ Divides(p, n)) => Divides(p, n - m)
PROOF
  <1> SUFFICES ASSUME NEW p \in Int, NEW m \in Int, NEW n \in Int,
                       Divides(p, m), Divides(p, n)
               PROVE  Divides(p, n - m)
    OBVIOUS
  <1>1. PICK q \in Int : m = p * q
    BY DEF Divides
  <1>2. PICK r \in Int : n = p * r
    BY DEF Divides
  <1>3. r - q \in Int
    BY <1>1, <1>2, SMT
  <1>4. n - m = p * (r - q)
    BY <1>1, <1>2, SMT
  <1>5. QED BY <1>3, <1>4 DEF Divides

LEMMA CommonDivisorAdd ==
  \A p, m, n \in Int :
    (Divides(p, m) /\ Divides(p, n - m)) => Divides(p, n)
PROOF
  <1> SUFFICES ASSUME NEW p \in Int, NEW m \in Int, NEW n \in Int,
                       Divides(p, m), Divides(p, n - m)
               PROVE  Divides(p, n)
    OBVIOUS
  <1>1. PICK q \in Int : m = p * q
    BY DEF Divides
  <1>2. PICK r \in Int : n - m = p * r
    BY DEF Divides
  <1>3. r + q \in Int
    BY <1>1, <1>2, SMT
  <1>4. n = (n - m) + m
    BY SMT
  <1>5. (n - m) + m = p * r + p * q
    BY <1>1, <1>2, SMT
  <1>6. p * r + p * q = p * (r + q)
    BY SMT
  <1>7. n = p * (r + q)
    BY <1>4, <1>5, <1>6
  <1>8. QED BY <1>3, <1>7 DEF Divides

LEMMA CommonDivisorsSubtract ==
  \A m, n \in Int :
    DivisorsOf(m) \cap DivisorsOf(n) =
      DivisorsOf(m) \cap DivisorsOf(n - m)
PROOF
  <1> SUFFICES ASSUME NEW m \in Int, NEW n \in Int
               PROVE  DivisorsOf(m) \cap DivisorsOf(n) =
                        DivisorsOf(m) \cap DivisorsOf(n - m)
    OBVIOUS
  <1>1. \A p :
          p \in DivisorsOf(m) \cap DivisorsOf(n) <=>
          p \in DivisorsOf(m) \cap DivisorsOf(n - m)
    BY CommonDivisorSubtract, CommonDivisorAdd, SMT DEF DivisorsOf
  <1>2. QED BY <1>1, SetExtensionality

------------------------------------------------------------------
THEOREM GCD3 == \A m, n \in Nat \ {0} : 
                    (n > m) => (GCD(m, n) = GCD(m, n-m))
PROOF
  <1> SUFFICES ASSUME NEW m \in Nat \ {0}, NEW n \in Nat \ {0},
                       n > m
               PROVE  GCD(m, n) = GCD(m, n - m)
    OBVIOUS
  <1>1. m \in Int /\ n \in Int
    BY SMT
  <1>2. DivisorsOf(m) \cap DivisorsOf(n) =
          DivisorsOf(m) \cap DivisorsOf(n - m)
    BY <1>1, CommonDivisorsSubtract
  <1>3. QED BY <1>2 DEF GCD
===================================================================
