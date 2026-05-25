--------------------------- MODULE GCD_GCD2 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
------------------------------------------------------------------
LEMMA InterComm == \A S, T : S \cap T = T \cap S
  OBVIOUS

THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
<1> TAKE m, n \in Nat \ {0}
<1>1 DivisorsOf(m) \cap DivisorsOf(n) = DivisorsOf(n) \cap DivisorsOf(m)
  BY InterComm
<1>2 GCD(m, n) = SetMax(DivisorsOf(m) \cap DivisorsOf(n))
  BY DEF GCD
<1>3 GCD(n, m) = SetMax(DivisorsOf(n) \cap DivisorsOf(m))
  BY DEF GCD
<1> QED
  BY <1>1, <1>2, <1>3
------------------------------------------------------------------
===================================================================