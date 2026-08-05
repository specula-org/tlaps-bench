----------------------------- MODULE BubbleSort_IsPermOfTransitiveDefs -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

Perms == { f \in [1..N -> 1..N] : 
                     \A p \in 1..N : \E q \in 1..N : f[p] = f[q] }

f ** g == [p \in 1..N |-> f[g[p]]]
   
IsPermOf(arr, brr) == \E f \in Perms : arr = (brr ** f)

=============================================================================

