----------------------------- MODULE BubbleSort_IsPermOfExchange -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

-----------------------------------------------------------------------------

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

-----------------------------------------------------------------------------

(* The transposition of 1..N that swaps positions p and q. *)
TransSwap(p, q) == [k \in 1..N |-> IF k = p THEN q ELSE IF k = q THEN p ELSE k]

(* Perms is in fact the set of ALL functions 1..N -> 1..N, since the          *)
(* membership predicate \A i : \E j : f[i] = f[j] is trivially true (j = i).  *)
LEMMA PermsIsAllFun == Perms = [1..N -> 1..N]
PROOF
  <1>1. Perms \subseteq [1..N -> 1..N]
    BY DEF Perms
  <1>2. [1..N -> 1..N] \subseteq Perms
    <2> SUFFICES ASSUME NEW f \in [1..N -> 1..N] PROVE f \in Perms
      OBVIOUS
    <2>1. ASSUME NEW k \in 1..N PROVE \E m \in 1..N : f[k] = f[m]
      <3> WITNESS k \in 1..N
      <3> QED OBVIOUS
    <2> QED BY <2>1 DEF Perms
  <1> QED BY <1>1, <1>2

(* The transposition is a member of Perms. *)
LEMMA TransSwapType ==
  ASSUME NEW p \in 1..N, NEW q \in 1..N
  PROVE  TransSwap(p, q) \in Perms
PROOF
  <1>1. TransSwap(p, q) \in [1..N -> 1..N]
    BY DEF TransSwap
  <1> QED BY <1>1, PermsIsAllFun

(* Swapping two values in A keeps it a function 1..N -> Int. *)
LEMMA SwapInFun ==
  ASSUME NEW A \in [1..N -> Int], NEW i \in 1..N, NEW j \in 1..N
  PROVE  [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
PROOF
  <1>1. A[i] \in Int
    OBVIOUS
  <1>2. A[j] \in Int
    OBVIOUS
  <1>3. [A EXCEPT ![i] = A[j]] \in [1..N -> Int]
    BY <1>2
  <1> QED BY <1>1, <1>3

(* The swapped array equals A composed with the transposition of i and j. *)
LEMMA SwapEqComp ==
  ASSUME NEW A \in [1..N -> Int], NEW i \in 1..N, NEW j \in 1..N
  PROVE  [A EXCEPT ![i] = A[j], ![j] = A[i]] = A ** TransSwap(i, j)
PROOF
  <1>1. TransSwap(i, j) \in [1..N -> 1..N]
    BY TransSwapType, PermsIsAllFun
  <1>2. A ** TransSwap(i, j) = [k \in 1..N |-> A[TransSwap(i, j)[k]]]
    BY DEF **
  <1>3. [A EXCEPT ![i] = A[j], ![j] = A[i]] = [k \in 1..N |-> A[TransSwap(i, j)[k]]]
    <2>1. DOMAIN [A EXCEPT ![i] = A[j], ![j] = A[i]] = 1..N
      OBVIOUS
    <2>2. ASSUME NEW k \in 1..N
          PROVE  [A EXCEPT ![i] = A[j], ![j] = A[i]][k] = A[TransSwap(i, j)[k]]
      <3>1. [A EXCEPT ![i] = A[j], ![j] = A[i]][k]
              = IF k = j THEN A[i] ELSE IF k = i THEN A[j] ELSE A[k]
        OBVIOUS
      <3>2. TransSwap(i, j)[k] = IF k = i THEN j ELSE IF k = j THEN i ELSE k
        BY DEF TransSwap
      <3>3. A[TransSwap(i, j)[k]]
              = IF k = i THEN A[j] ELSE IF k = j THEN A[i] ELSE A[k]
        BY <3>2
      <3> QED BY <3>1, <3>3
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3

THEOREM IsPermOfExchange ==
           \A A \in [1..N -> Int],  i, j \in 1..N :
             /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
PROOF
  <1> SUFFICES ASSUME NEW A \in [1..N -> Int], NEW i \in 1..N, NEW j \in 1..N
               PROVE  /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
                      /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
    OBVIOUS
  <1>1. [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
    BY SwapInFun
  <1>2. IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
    <2>1. TransSwap(i, j) \in Perms
      BY TransSwapType
    <2>2. [A EXCEPT ![i] = A[j], ![j] = A[i]] = A ** TransSwap(i, j)
      BY SwapEqComp
    <2> QED BY <2>1, <2>2 DEF IsPermOf
  <1> QED BY <1>1, <1>2

----------------------------------------------------------------------------

VARIABLES A, A0, i, j, pc

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================

