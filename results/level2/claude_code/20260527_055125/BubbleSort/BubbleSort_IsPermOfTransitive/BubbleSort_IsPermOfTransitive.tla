----------------------------- MODULE BubbleSort_IsPermOfTransitive -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

-----------------------------------------------------------------------------

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

THEOREM IsPermOfTransitive ==
          \A A, B, C \in [1..N -> Int] :
             IsPermOf(A, B) /\ IsPermOf(B, C) => IsPermOf(A, C)
PROOF
  <1> SUFFICES ASSUME NEW A \in [1..N -> Int], NEW B \in [1..N -> Int],
                      NEW C \in [1..N -> Int],
                      IsPermOf(A, B), IsPermOf(B, C)
               PROVE IsPermOf(A, C)
      OBVIOUS
  <1>1. PICK f \in Perms : A = (B ** f)
      BY DEF IsPermOf
  <1>2. PICK g \in Perms : B = (C ** g)
      BY DEF IsPermOf
  <1>f. f \in [1..N -> 1..N]
      BY <1>1 DEF Perms
  <1>g. g \in [1..N -> 1..N]
      BY <1>2 DEF Perms
  <1>3. (g ** f) \in [1..N -> 1..N]
      <2>1. \A k \in 1..N : g[f[k]] \in 1..N
          BY <1>f, <1>g
      <2>2. QED
          BY <2>1 DEF **
  <1>4. (g ** f) \in Perms
      <2>1. \A k \in 1..N : \E m \in 1..N : (g ** f)[k] = (g ** f)[m]
          <3> TAKE k \in 1..N
          <3> WITNESS k \in 1..N
          <3> QED
              OBVIOUS
      <2>2. QED
          BY <1>3, <2>1 DEF Perms
  <1>5. A = (C ** (g ** f))
      <2>1. \A k \in 1..N : A[k] = (C ** (g ** f))[k]
          <3> TAKE k \in 1..N
          <3>1. A[k] = B[f[k]]
              BY <1>1 DEF **
          <3>2. f[k] \in 1..N
              BY <1>f
          <3>3. B[f[k]] = C[g[f[k]]]
              BY <1>2, <3>2 DEF **
          <3>4. (C ** (g ** f))[k] = C[g[f[k]]]
              BY <1>f DEF **
          <3>5. QED
              BY <3>1, <3>3, <3>4
      <2>2. (C ** (g ** f)) \in [1..N -> Int]
          <3>1. \A k \in 1..N : C[g[f[k]]] \in Int
              BY <1>3 DEF **
          <3>2. QED
              BY <3>1 DEF **
      <2>3. QED
          BY <2>1, <2>2
  <1>6. QED
      BY <1>4, <1>5 DEF IsPermOf
----------------------------------------------------------------------------

VARIABLES A, A0, i, j, pc

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================

