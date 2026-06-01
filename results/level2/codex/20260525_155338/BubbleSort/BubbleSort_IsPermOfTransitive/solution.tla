----------------------------- MODULE BubbleSort_IsPermOfTransitive -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

-----------------------------------------------------------------------------

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

LEMMA PermsCompose ==
  \A f, g \in Perms : g ** f \in Perms
PROOF
  BY SMT DEF Perms, **

LEMMA ComposeAssoc ==
  \A C \in [1..N -> Int] : \A f, g \in Perms :
    (C ** g) ** f = C ** (g ** f)
PROOF
  <1>1. SUFFICES ASSUME NEW C \in [1..N -> Int],
                       NEW f \in Perms,
                       NEW g \in Perms
                PROVE  (C ** g) ** f = C ** (g ** f)
    OBVIOUS
  <1>2. f \in [1..N -> 1..N] /\ g \in [1..N -> 1..N]
    BY <1>1 DEF Perms
  <1>3. \A i \in 1..N : ((C ** g) ** f)[i] = (C ** (g ** f))[i]
  PROOF
    <2>1. SUFFICES ASSUME NEW i \in 1..N
                   PROVE  ((C ** g) ** f)[i] = (C ** (g ** f))[i]
      OBVIOUS
    <2>2. f[i] \in 1..N
      BY <1>2, <2>1
    <2>3. g[f[i]] \in 1..N
      BY <1>2, <2>2
    <2>4. (g ** f)[i] = g[f[i]]
      BY <2>1 DEF **
    <2>5. ((C ** g) ** f)[i] = (C ** g)[f[i]]
      BY <2>1 DEF **
    <2>6. (C ** g)[f[i]] = C[g[f[i]]]
      BY <2>2 DEF **
    <2>7. (C ** (g ** f))[i] = C[(g ** f)[i]]
      BY <2>1 DEF **
    <2>8. QED
      BY <2>4, <2>5, <2>6, <2>7
  <1>4. QED
    BY <1>3 DEF **

THEOREM IsPermOfTransitive == 
          \A A, B, C \in [1..N -> Int] : 
             IsPermOf(A, B) /\ IsPermOf(B, C) => IsPermOf(A, C)
PROOF
  <1>1. SUFFICES ASSUME NEW A \in [1..N -> Int],
                       NEW B \in [1..N -> Int],
                       NEW C \in [1..N -> Int],
                       IsPermOf(A, B),
                       IsPermOf(B, C)
                PROVE  IsPermOf(A, C)
    BY DEF IsPermOf
  <1>2. PICK f \in Perms : A = (B ** f)
    BY <1>1 DEF IsPermOf
  <1>3. PICK g \in Perms : B = (C ** g)
    BY <1>1 DEF IsPermOf
  <1>4. g ** f \in Perms
    BY <1>2, <1>3, PermsCompose
  <1>5. A = C ** (g ** f)
    BY <1>2, <1>3, ComposeAssoc
  <1>6. QED
    BY <1>4, <1>5 DEF IsPermOf
----------------------------------------------------------------------------

VARIABLES A, A0, i, j, pc

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
