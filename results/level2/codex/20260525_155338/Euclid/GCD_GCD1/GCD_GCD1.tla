--------------------------- MODULE GCD_GCD1 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
SMT == TRUE (*{ by (prover:"smt3") }*)

IsMax(i, S) == /\ i \in S
               /\ \A j \in S : i >= j

LEMMA SetMaxUnique ==
  \A S \in SUBSET Int : \A k \in Int : IsMax(k, S) => SetMax(S) = k
PROOF
  <1>1. ASSUME NEW S \in SUBSET Int, NEW k \in Int, IsMax(k, S)
        PROVE SetMax(S) = k
    <2>1. IsMax(SetMax(S), S)
      BY <1>1 DEF IsMax, SetMax
    <2>2. SetMax(S) \in Int
      BY <1>1, <2>1 DEF IsMax
    <2>3. SetMax(S) >= k
      BY <1>1, <2>1 DEF IsMax
    <2>4. k >= SetMax(S)
      BY <1>1, <2>1 DEF IsMax
    <2>5. QED
      BY <1>1, <2>2, <2>3, <2>4, SMT
  <1>2. QED
    BY <1>1

LEMMA DivisorLeSelf ==
  \A m \in Nat \ {0} : \A p \in Int : Divides(p, m) => p <= m
PROOF
  BY SMT DEF Divides

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF
  <1>1. ASSUME NEW m \in Nat \ {0}
        PROVE GCD(m, m) = m
    <2>1. m \in DivisorsOf(m) \cap DivisorsOf(m)
      <3>1. m \in Int
        BY SMT
      <3>2. 1 \in Int /\ m = m * 1
        BY SMT
      <3>3. Divides(m, m)
        BY <3>2 DEF Divides
      <3>4. m \in DivisorsOf(m)
        BY <3>1, <3>3 DEF DivisorsOf
      <3>5. QED
        BY <3>4
    <2>2. \A j \in DivisorsOf(m) \cap DivisorsOf(m) : m >= j
      BY <2>1, DivisorLeSelf, SMT DEF DivisorsOf
    <2>3. IsMax(m, DivisorsOf(m) \cap DivisorsOf(m))
      BY <2>1, <2>2 DEF IsMax
    <2>4. DivisorsOf(m) \cap DivisorsOf(m) \in SUBSET Int
      BY SMT DEF DivisorsOf
    <2>5. SetMax(DivisorsOf(m) \cap DivisorsOf(m)) = m
      BY <2>3, <2>4, SetMaxUnique, SMT
    <2>6. QED
      BY <2>5 DEF GCD
  <1>2. QED
    BY <1>1
------------------------------------------------------------------
------------------------------------------------------------------
===================================================================
