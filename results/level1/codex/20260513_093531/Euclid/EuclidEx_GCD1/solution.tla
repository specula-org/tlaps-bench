---- MODULE EuclidEx_GCD1 ----
EXTENDS Integers, TLAPS
(* ---- Content from module GCD ---- *)
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF
  <1>1. ASSUME NEW m \in Nat \ {0}
        PROVE  GCD(m, m) = m
    <2>1. m \in DivisorsOf(m) /\ \A j \in DivisorsOf(m) : m >= j
      BY SMT DEF DivisorsOf, Divides
    <2>2. m \in DivisorsOf(m) \cap DivisorsOf(m)
      BY <2>1
    <2>3. \A j \in DivisorsOf(m) \cap DivisorsOf(m) : m >= j
      BY <2>1
    <2>4. SetMax(DivisorsOf(m) \cap DivisorsOf(m)) = m
      BY <2>2, <2>3 DEF SetMax
    <2> QED BY <2>4 DEF GCD
  <1> QED BY <1>1

========================================
