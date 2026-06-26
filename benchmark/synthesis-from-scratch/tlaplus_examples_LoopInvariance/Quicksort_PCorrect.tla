----------------------------- MODULE Quicksort_PCorrect -----------------------------

EXTENDS Quicksort

PCorrect == (pc = "Done") => 
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q] 

THEOREM Spec => []PCorrect
PROOF OBVIOUS
=============================================================================

