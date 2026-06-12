---- MODULE ProvenHelperModule ----
VARIABLE x
Inv == x \in {0, 1}
THEOREM Real == Inv => Inv
<1>1. TRUE OBVIOUS
<1> QED BY <1>1 DEF Inv
====
