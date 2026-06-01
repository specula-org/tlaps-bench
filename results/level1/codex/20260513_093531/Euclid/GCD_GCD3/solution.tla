--------------------------- MODULE GCD_GCD3 ---------------------------
EXTENDS Integers
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
                  PROVE GCD(m, n) = GCD(m, n-m)
    OBVIOUS
  <1>2. DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(m) \cap DivisorsOf(n-m)
    PROOF
      <2>1. \A p : p \in DivisorsOf(m) \cap DivisorsOf(n)
                    <=> p \in DivisorsOf(m) \cap DivisorsOf(n-m)
        PROOF
          <3>1. ASSUME NEW p, p \in DivisorsOf(m) \cap DivisorsOf(n)
                PROVE p \in DivisorsOf(m) \cap DivisorsOf(n-m)
            PROOF
              <4>1. p \in DivisorsOf(m) /\ p \in DivisorsOf(n) BY <3>1
              <4>2. p \in Int BY <4>1 DEF DivisorsOf
              <4>3. PICK q \in Int : m = p * q BY <4>1 DEF DivisorsOf, Divides
              <4>4. PICK r \in Int : n = p * r BY <4>1 DEF DivisorsOf, Divides
              <4>5. n - m = p * (r - q) BY <4>2, <4>3, <4>4
              <4>6. r - q \in Int BY <4>3, <4>4
              <4>7. Divides(p, n-m) BY <4>5, <4>6 DEF Divides
              <4>8. p \in DivisorsOf(n-m) BY <4>2, <4>7 DEF DivisorsOf
              <4> QED BY <4>1, <4>8
          <3>2. ASSUME NEW p, p \in DivisorsOf(m) \cap DivisorsOf(n-m)
                PROVE p \in DivisorsOf(m) \cap DivisorsOf(n)
            PROOF
              <4>1. p \in DivisorsOf(m) /\ p \in DivisorsOf(n-m) BY <3>2
              <4>2. p \in Int BY <4>1 DEF DivisorsOf
              <4>3. PICK q \in Int : m = p * q BY <4>1 DEF DivisorsOf, Divides
              <4>4. PICK r \in Int : n - m = p * r BY <4>1 DEF DivisorsOf, Divides
              <4>5. n = p * (q + r) BY <4>2, <4>3, <4>4
              <4>6. q + r \in Int BY <4>3, <4>4
              <4>7. Divides(p, n) BY <4>5, <4>6 DEF Divides
              <4>8. p \in DivisorsOf(n) BY <4>2, <4>7 DEF DivisorsOf
              <4> QED BY <4>1, <4>8
          <3> QED BY <3>1, <3>2
      <2> QED BY <2>1
  <1> QED BY <1>2 DEF GCD

===================================================================
