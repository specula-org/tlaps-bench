----------------------------- MODULE BubbleSort_line202 -----------------------------

EXTENDS BubbleSort

IsSortedTo(A, i) == \A j, k \in 1..i : (j =< k) => (A[j] =< A[k])

IsSorted(A) == IsSortedTo(A, N)

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
PROOF OBVIOUS

=============================================================================

