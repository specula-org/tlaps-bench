---- MODULE EuclidEx_GCD3 ----
EXTENDS Integers, TLAPS
(* ---- Content from module GCD ---- *)
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
  PROOF OMITTED

------------------------------------------------------------------
THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
  PROOF OMITTED

------------------------------------------------------------------
THEOREM GCD3 == \A m, n \in Nat \ {0} : 
                    (n > m) => (GCD(m, n) = GCD(m, n-m))
PROOF
  <1>1. SUFFICES ASSUME NEW m \in Nat \ {0}, NEW n \in Nat \ {0}, n > m
                 PROVE  GCD(m, n) = GCD(m, n-m)
    OBVIOUS
  <1>2. DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n-m)
    <2>1. \A p : p \in DivisorsOf(m) \cap DivisorsOf(n)
                 <=> p \in DivisorsOf(m) \cap DivisorsOf(n-m)
      <3>1. TAKE p
      <3>2. ASSUME p \in DivisorsOf(m) \cap DivisorsOf(n)
             PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n-m)
        <4>1. p \in Int /\ Divides(p, m) /\ Divides(p, n)
          BY <3>2 DEF DivisorsOf
        <4>2. PICK q \in Int : m = p * q
          BY <4>1 DEF Divides
        <4>3. PICK r \in Int : n = p * r
          BY <4>1 DEF Divides
        <4>4. m \in Int /\ n \in Int /\ p * q \in Int /\ p * r \in Int
          BY <1>1, <4>2, <4>3
        <4>5. n - m = p * r - p * q
          BY <4>2, <4>3, <4>4
        <4>6. p * r - p * q = p * (r - q)
          BY <4>1, <4>2, <4>3, <4>4, SMT
        <4>7. n - m = p * (r - q)
          BY <4>5, <4>6
        <4>8. r - q \in Int
          BY <4>2, <4>3
        <4>9. Divides(p, n-m)
          BY <4>7, <4>8 DEF Divides
        <4> QED
          BY <4>1, <4>9 DEF DivisorsOf
      <3>3. ASSUME p \in DivisorsOf(m) \cap DivisorsOf(n-m)
             PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n)
        <4>1. p \in Int /\ Divides(p, m) /\ Divides(p, n-m)
          BY <3>3 DEF DivisorsOf
        <4>2. PICK q \in Int : m = p * q
          BY <4>1 DEF Divides
        <4>3. PICK r \in Int : n - m = p * r
          BY <4>1 DEF Divides
        <4>4. m \in Int /\ n \in Int /\ p * q \in Int /\ p * r \in Int
          BY <1>1, <4>2, <4>3
        <4>5. n - m + m = n
          BY <4>4
        <4>6. n = p * r + p * q
          BY <4>2, <4>3, <4>4, <4>5, Z3
        <4>7. p * r + p * q = p * (r + q)
          BY <4>1, <4>2, <4>3, <4>4, SMT
        <4>8. n = p * (r + q)
          BY <4>6, <4>7
        <4>9. r + q \in Int
          BY <4>2, <4>3
        <4>10. Divides(p, n)
          BY <4>8, <4>9 DEF Divides
        <4> QED
          BY <4>1, <4>10 DEF DivisorsOf
      <3> QED
        BY <3>2, <3>3
    <2> QED
      BY <2>1
  <1> QED
    BY <1>2 DEF GCD

========================================
