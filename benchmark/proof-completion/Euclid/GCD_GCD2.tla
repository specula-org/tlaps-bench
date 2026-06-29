--------------------------- MODULE GCD_GCD2 ---------------------------
EXTENDS Integers
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF OMITTED
THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
PROOF OBVIOUS
===================================================================