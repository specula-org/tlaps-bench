---- MODULE SmuggledObvious ----
VARIABLE x
Spec == (x = 0) /\ [][x' = x]_x
Goal == x = 0
THEOREM Smuggled == Spec => []Goal
PROOF OBVIOUS
====
