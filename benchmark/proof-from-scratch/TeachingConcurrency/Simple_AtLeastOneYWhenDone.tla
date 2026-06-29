------------------------------- MODULE Simple_AtLeastOneYWhenDone -------------------------------

EXTENDS Simple

AtLeastOneYWhenDone == (\A i \in 0 .. N-1 : pc[i] = "Done") => \E i \in 0 .. N-1 : y[i] = 1

THEOREM Spec => []AtLeastOneYWhenDone
PROOF OBVIOUS
=============================================================================

