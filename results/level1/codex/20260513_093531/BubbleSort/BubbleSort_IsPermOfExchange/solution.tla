----------------------------- MODULE BubbleSort_IsPermOfExchange -----------------------------
(***************************************************************************)
(* This module contains a PlusCal description of the classic Bubble Sort   *)
(* algorithm and a TLAPLUS-checked proof of its correctness.               *)
(***************************************************************************)
EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1
  (*************************************************************************)
  (* The algorithm is actually correct for N = 0, but allowing for that    *)
  (* case complicates the proof a bit, so I decided not to handle that     *)
  (* possibility.                                                          *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Here are some definitions used for stating and proving correctness.     *)
(* For simplicity, I decide to write an algorithm that sorts               *)
(* integer-valued arrays (functions) indexed by (with domain) 1..N.        *)
(*                                                                         *)
(* The obvious correctness condition is that, at termination, the array    *)
(* should be sorted--expressed by IsSorted.                                *)
(***************************************************************************)
IsSortedFromTo(A, i, j) == \A p, q \in i..j : (p =< q) => (A[p] =< A[q])

IsSortedTo(A, i) == \A j, k \in 1..i : (j =< k) => (A[j] =< A[k])

IsSorted(A) == IsSortedTo(A, N)

(***************************************************************************)
(* The less obvious correctness condition is that the array should be a    *)
(* permutation of its initial value.  I define IsPermOf(A, B) to mean that *)
(* arrays A and B are permutations of one another.  I start by defining    *)
(* Perms to be the set of permutations of (sequences of length N           *)
(* containing all of) the numbers from 1 through N.                        *)
(***************************************************************************)
Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

(***************************************************************************)
(* Next, I define two useful permutations of 1..N , the identity Id and    *)
(* the permutation of 1..N that just exchanges two numbers.  (If the       *)
(* numbers are the same, it's the identity permutation.)                   *)
(***************************************************************************)
Id == [i \in 1..N |-> i] 

Exchange(i, j) == [Id EXCEPT ![i] = j, ![j] = i]

(***************************************************************************)
(* Here are some theorems that I figured would be useful for proving the   *)
(* correctness of Bubble Sort.                                             *)
(***************************************************************************)
THEOREM IdAPerm == Id \in Perms
  PROOF OMITTED

THEOREM IdIdentity == \A A \in [1..N -> Int] : A ** Id = A
  PROOF OMITTED

THEOREM IsPermOfReflexive == \A A \in [1..N -> Int]  : IsPermOf(A, A)
  PROOF OMITTED

THEOREM ExchangeAPerm == \A i, j \in 1..N : Exchange(i, j) \in Perms
  PROOF OMITTED

THEOREM IsPermOfExchange == 
           \A A \in [1..N -> Int],  i, j \in 1..N :
             /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
PROOF
  <1>1. TAKE A \in [1..N -> Int]
  <1>2. TAKE i \in 1..N
  <1>3. TAKE j \in 1..N
  <1>4. [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
    BY <1>1, <1>2, <1>3 DEF Int
  <1>5. [A EXCEPT ![i] = A[j], ![j] = A[i]] = A ** Exchange(i, j)
  PROOF
    <2>1. [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
      BY <1>4
    <2>2. Exchange(i, j) \in [1..N -> 1..N]
      BY <1>2, <1>3, ExchangeAPerm DEF Perms
    <2>3. A ** Exchange(i, j) \in [1..N -> Int]
      BY <1>1, <2>2 DEF **
    <2>4. \A k \in 1..N : [A EXCEPT ![i] = A[j], ![j] = A[i]][k]
                         = (A ** Exchange(i, j))[k]
    PROOF
      <3>1. TAKE k \in 1..N
      <3>2. CASE k = i
        BY <1>1, <1>2, <1>3, <3>1 DEF **, Exchange, Id
      <3>3. CASE k = j
        BY <1>1, <1>2, <1>3, <3>1 DEF **, Exchange, Id
      <3>4. CASE k # i /\ k # j
        BY <1>1, <1>2, <1>3, <3>1 DEF **, Exchange, Id
      <3>5. QED BY <3>2, <3>3, <3>4
    <2>5. QED BY <2>1, <2>3, <2>4
  <1>6. IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
    BY <1>2, <1>3, <1>5, ExchangeAPerm DEF IsPermOf
  <1>7. QED BY <1>4, <1>6

=============================================================================
