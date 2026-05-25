----------------------------- MODULE BubbleSort_line202 -----------------------------
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







----------------------------------------------------------------------------
(***************************************************************************)
(* Here is the PlusCal algorithm followed by its TLA+ translation.  It was *)
(* model checked, with the asserts not commented out, for N = 4, with Int  *)
(* replaced by a set of integers containing 4 distinct elements.           *)
(***************************************************************************)
(*
--fair algorithm BubbleSort {
    variables A \in [1..N -> Int], A0 = A, i = 1, j = 1;
    { while (i < N)
       { \* assert IsSortedTo(A, i) /\ IsPermOf(A, A0);
         j := i+1 ;
         while (j > 1  /\  A[j-1] > A[j]) 
           { \* assert IsSortedTo(A, j-1) /\ IsSortedFromTo(A, j, i+1) /\ IsPermOf(A, A0) ;
             A[j-1] := A[j] || A[j] := A[j-1] ;
             j := j-1 ;        
           } ;
         i := i+1 ;
       } ;
      \* assert IsSorted(A) /\ IsPermOf(A, A0)
    } 
} 
*)
\* BEGIN TRANSLATION
VARIABLES A, A0, i, j, pc

vars == << A, A0, i, j, pc >>

Init == (* Global variables *)
        /\ A \in [1..N -> Int]
        /\ A0 = A
        /\ i = 1
        /\ j = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < N
               THEN /\ j' = i+1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ j' = j
         /\ UNCHANGED << A, A0, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF j > 1  /\  A[j-1] > A[j]
               THEN /\ A' = [A EXCEPT ![j-1] = A[j],
                                      ![j] = A[j-1]]
                    /\ j' = j-1
                    /\ pc' = "Lbl_2"
                    /\ i' = i
               ELSE /\ i' = i+1
                    /\ pc' = "Lbl_1"
                    /\ UNCHANGED << A, j >>
         /\ A0' = A0

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Next comes the definition of the inductive invariant Inv.  Its          *)
(* invariance was checked by TLC for N = 4, and its inductive invariance   *)
(* was checked for N = 3 (with Int replaced by a set of 3 integers).       *)
(***************************************************************************)
TypeOK == /\ i \in 1..N
          /\ j \in 1..N
          /\ A \in [1..N -> Int]
          /\ A0 \in [1..N -> Int]
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}
          
RealInv ==
  /\ pc = "Lbl_1" => /\ IsSortedTo(A, i)
                     /\ IsPermOf(A, A0)
  /\ pc = "Lbl_2" => /\ j \in 1..(i+1)
                     /\ i < N
                     /\ IsSortedTo(A, j-1)
                     /\ IsSortedFromTo(A, j, i+1)
                     /\ \A p \in 1..(j-1), q \in (j+1)..(i+1) : A[p] =< A[q]
                     /\ IsPermOf(A, A0)
                     
  /\ pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0)
  
Inv == TypeOK /\ RealInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* Permutation helper lemmas.                                              *)
(***************************************************************************)
LEMMA PermsDef == Perms = [1..N -> 1..N]
<1>1. \A f \in [1..N -> 1..N] : \A a \in 1..N : \E b \in 1..N : f[a] = f[b]
  OBVIOUS
<1> QED BY <1>1 DEF Perms

LEMMA IdInPerms == Id \in Perms
<1>1. Id \in [1..N -> 1..N]  BY DEF Id
<1> QED BY <1>1, PermsDef

LEMMA ExchangeInPerms ==
  ASSUME NEW k, k \in 1..N, NEW l, l \in 1..N
  PROVE  Exchange(k, l) \in [1..N -> 1..N]
<1>1. Id \in [1..N -> 1..N]  BY DEF Id
<1> QED BY <1>1 DEF Exchange

LEMMA PermCompose ==
  ASSUME NEW Base, Base \in [1..N -> Int],
         NEW Cur, IsPermOf(Cur, Base),
         NEW e, e \in [1..N -> 1..N]
  PROVE  IsPermOf(Cur ** e, Base)
<1>1. PICK f \in Perms : Cur = Base ** f  BY DEF IsPermOf
<1>2. f \in [1..N -> 1..N]  BY <1>1, PermsDef
<1>3. f ** e \in [1..N -> 1..N]  BY <1>2 DEF **
<1>4. f ** e \in Perms  BY <1>3, PermsDef
<1>5. Cur ** e = Base ** (f ** e)
  <2>1. Cur ** e = [m \in 1..N |-> Cur[e[m]]]  BY DEF **
  <2>2. \A m \in 1..N : Cur[e[m]] = Base[f[e[m]]]
    <3> TAKE m \in 1..N
    <3>1. e[m] \in 1..N  OBVIOUS
    <3> QED BY <1>1, <3>1 DEF **
  <2>3. Base ** (f ** e) = [m \in 1..N |-> Base[(f ** e)[m]]]  BY DEF **
  <2>4. \A m \in 1..N : (f ** e)[m] = f[e[m]]  BY DEF **
  <2> QED BY <2>1, <2>2, <2>3, <2>4
<1> QED BY <1>4, <1>5 DEF IsPermOf

LEMMA SwapIsCompose ==
  ASSUME NEW B, B \in [1..N -> Int],
         NEW k, k \in 1..N, NEW l, l \in 1..N, k # l
  PROVE  [B EXCEPT ![k] = B[l], ![l] = B[k]] = B ** Exchange(k, l)
<1>1. Id \in [1..N -> 1..N]  BY DEF Id
<1>2. Exchange(k, l) = [Id EXCEPT ![k] = l, ![l] = k]  BY DEF Exchange
<1>3. Exchange(k, l) \in [1..N -> 1..N]  BY <1>1, <1>2
<1>4. \A m \in 1..N : Exchange(k, l)[m] = (IF m = l THEN k ELSE IF m = k THEN l ELSE m)
  BY <1>1, <1>2 DEF Id
<1>5. B ** Exchange(k, l) = [m \in 1..N |-> B[Exchange(k, l)[m]]]  BY DEF **
<1>6. \A m \in 1..N : [B EXCEPT ![k] = B[l], ![l] = B[k]][m]
                       = (IF m = l THEN B[k] ELSE IF m = k THEN B[l] ELSE B[m])
  OBVIOUS
<1>7. \A m \in 1..N : [B EXCEPT ![k] = B[l], ![l] = B[k]][m] = B[Exchange(k, l)[m]]
  <2> TAKE m \in 1..N
  <2>1. Exchange(k, l)[m] \in 1..N  BY <1>3
  <2> QED BY <1>4, <1>6
<1>8. [B EXCEPT ![k] = B[l], ![l] = B[k]] \in [1..N -> Int]  OBVIOUS
<1> QED BY <1>5, <1>7, <1>8

LEMMA PermOfRefl ==
  ASSUME NEW B, B \in [1..N -> Int]
  PROVE  IsPermOf(B, B)
<1>1. Id \in Perms  BY IdInPerms
<1>2. B ** Id = B
  <2>1. B ** Id = [m \in 1..N |-> B[Id[m]]]  BY DEF **
  <2>2. \A m \in 1..N : Id[m] = m  BY DEF Id
  <2>3. B ** Id = [m \in 1..N |-> B[m]]  BY <2>1, <2>2
  <2> QED BY <2>3
<1> QED BY <1>1, <1>2 DEF IsPermOf
-----------------------------------------------------------------------------
(***************************************************************************)
(* Finally, we get to the theorem asserting correctness of the algorithm   *)
(* and its proof.                                                          *)
(***************************************************************************)
THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <2> USE NAssumption DEF Init
  <2>1. TypeOK  BY DEF TypeOK
  <2>2. IsSortedTo(A, i)
    BY DEF IsSortedTo
  <2>3. IsPermOf(A, A0)
    BY PermOfRefl
  <2>4. RealInv
    BY <2>2, <2>3 DEF RealInv
  <2> QED BY <2>1, <2>4 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
              PROVE  Inv'
    OBVIOUS
  <2> USE NAssumption
  <2>t. TypeOK  BY DEF Inv
  <2>1. CASE Lbl_1
    <3> USE <2>1 DEF Lbl_1
    <3>p. pc = "Lbl_1"  OBVIOUS
    <3>inv. IsSortedTo(A, i) /\ IsPermOf(A, A0)
      BY <3>p DEF Inv, RealInv
    <3>unch. A' = A /\ A0' = A0 /\ i' = i
      OBVIOUS
    <3>1. CASE i < N
      <4>def. j' = i + 1 /\ pc' = "Lbl_2"  BY <3>1
      <4>tok. TypeOK'
        BY <3>1, <3>unch, <4>def, <2>t DEF TypeOK
      <4>ri. RealInv'
        <5>a. pc' = "Lbl_2"  BY <4>def
        <5>b. /\ j' \in 1..(i' + 1)
              /\ i' < N
              /\ IsSortedTo(A', j' - 1)
              /\ IsSortedFromTo(A', j', i' + 1)
              /\ \A p \in 1..(j' - 1), q \in (j' + 1)..(i' + 1) : A'[p] =< A'[q]
              /\ IsPermOf(A', A0')
          <6>1. j' \in 1..(i' + 1)  BY <3>unch, <4>def, <2>t DEF TypeOK
          <6>2. i' < N  BY <3>1, <3>unch
          <6>3. IsSortedTo(A', j' - 1)
            <7>1. j' - 1 = i  BY <4>def, <2>t DEF TypeOK
            <7> QED BY <3>inv, <3>unch, <7>1
          <6>4. IsSortedFromTo(A', j', i' + 1)
            <7> SUFFICES \A p, q \in (i + 1)..(i + 1) : (p =< q) => A'[p] =< A'[q]
              BY <3>unch, <4>def DEF IsSortedFromTo
            <7> TAKE p, q \in (i + 1)..(i + 1)
            <7> HAVE p =< q
            <7>1. i + 1 \in 1..N  BY <3>1, <2>t DEF TypeOK
            <7> QED BY <3>unch, <7>1, <2>t DEF TypeOK
          <6>5. \A p \in 1..(j' - 1), q \in (j' + 1)..(i' + 1) : A'[p] =< A'[q]
            <7>1. (j' + 1)..(i' + 1) = {}  BY <4>def, <3>unch, <2>t DEF TypeOK
            <7> QED BY <7>1
          <6>6. IsPermOf(A', A0')  BY <3>inv, <3>unch
          <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5, <6>6
        <5> QED BY <5>a, <5>b DEF RealInv
      <4> QED BY <4>tok, <4>ri DEF Inv
    <3>2. CASE ~(i < N)
      <4>0. i = N  BY <2>t, <3>2, NAssumption DEF TypeOK
      <4>def. pc' = "Done" /\ j' = j  BY <3>2
      <4>tok. TypeOK'
        BY <3>unch, <4>def, <2>t DEF TypeOK
      <4>ri. RealInv'
        <5>a. pc' = "Done"  BY <4>def
        <5>b. IsSorted(A') /\ IsPermOf(A', A0')
          <6>1. IsSorted(A')
            BY <3>inv, <3>unch, <4>0 DEF IsSorted
          <6>2. IsPermOf(A', A0')  BY <3>inv, <3>unch
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>a, <5>b DEF RealInv
      <4> QED BY <4>tok, <4>ri DEF Inv
    <3> QED BY <3>1, <3>2
  <2>2. CASE Lbl_2
    <3> USE <2>2 DEF Lbl_2
    <3>p. pc = "Lbl_2"  OBVIOUS
    <3>inv. /\ j \in 1..(i + 1)
            /\ i < N
            /\ IsSortedTo(A, j - 1)
            /\ IsSortedFromTo(A, j, i + 1)
            /\ \A p \in 1..(j - 1), q \in (j + 1)..(i + 1) : A[p] =< A[q]
            /\ IsPermOf(A, A0)
      BY <3>p DEF Inv, RealInv
    <3>a0. A0' = A0  OBVIOUS
    <3>1. CASE j > 1 /\ A[j-1] > A[j]
      <4>def. /\ A' = [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]]
              /\ j' = j - 1
              /\ pc' = "Lbl_2"
              /\ i' = i
        BY <3>1
      <4>jm1. j - 1 \in 1..N  BY <3>1, <2>t DEF TypeOK
      <4>jn.  j \in 1..N  BY <2>t DEF TypeOK
      <4>jm1b. j - 1 \in 1..(j - 1)  BY <3>1, <2>t DEF TypeOK
      <4>jne. j - 1 # j  BY <2>t DEF TypeOK
      <4>aint. A[j] \in Int /\ A[j-1] \in Int  BY <4>jm1, <4>jn, <2>t DEF TypeOK
      <4>e1. A'[j - 1] = A[j]
        BY <4>def, <4>jm1, <4>jn, <4>jne, <2>t DEF TypeOK
      <4>e2. A'[j] = A[j - 1]
        BY <4>def, <4>jn, <2>t DEF TypeOK
      <4>e3. \A m \in 1..N : (m # j - 1 /\ m # j) => A'[m] = A[m]
        BY <4>def, <2>t DEF TypeOK
      <4>tok. TypeOK'
        <5>1. A' \in [1..N -> Int]
          BY <4>def, <4>jm1, <4>jn, <2>t DEF TypeOK
        <5>2. j' \in 1..N  BY <4>def, <4>jm1
        <5> QED BY <5>1, <5>2, <4>def, <2>t, <3>a0 DEF TypeOK
      <4>ri. RealInv'
        <5>a. pc' = "Lbl_2"  BY <4>def
        <5>c1. j' \in 1..(i' + 1)  BY <4>def, <3>inv, <3>1, <2>t DEF TypeOK
        <5>c2. i' < N  BY <4>def, <3>inv
        <5>c3. IsSortedTo(A', j' - 1)
          <6> SUFFICES \A p, q \in 1..(j' - 1) : (p =< q) => A'[p] =< A'[q]
            BY DEF IsSortedTo
          <6> TAKE p, q \in 1..(j' - 1)
          <6> HAVE p =< q
          <6>1. p \in 1..(j - 1) /\ q \in 1..(j - 1)  BY <4>def, <4>jn
          <6>2. p \in 1..N /\ q \in 1..N  BY <6>1, <4>jn
          <6>3. p # j - 1 /\ p # j /\ q # j - 1 /\ q # j  BY <4>def, <4>jn
          <6>4. A'[p] = A[p] /\ A'[q] = A[q]  BY <6>2, <6>3, <4>e3
          <6>5. A[p] =< A[q]  BY <6>1, <3>inv DEF IsSortedTo
          <6> QED BY <6>4, <6>5
        <5>c4. IsSortedFromTo(A', j', i' + 1)
          <6> SUFFICES \A p, q \in (j - 1)..(i + 1) : (p =< q) => A'[p] =< A'[q]
            BY <4>def DEF IsSortedFromTo
          <6> TAKE p, q \in (j - 1)..(i + 1)
          <6> HAVE p =< q
          <6>dom. p \in 1..N /\ q \in 1..N  BY <3>1, <3>inv, <4>jn, <2>t DEF TypeOK
          <6>1. CASE p = j - 1
            <7>1. A'[p] = A[j]  BY <6>1, <4>e1
            <7>2. CASE q = j - 1
              <8>1. A'[q] = A[j]  BY <7>2, <4>e1
              <8> QED BY <7>1, <8>1, <4>aint
            <7>3. CASE q = j
              <8>1. A'[q] = A[j - 1]  BY <7>3, <4>e2
              <8> QED BY <7>1, <8>1, <3>1, <4>aint
            <7>4. CASE q # j - 1 /\ q # j
              <8>0. q \in j..(i + 1)  BY <7>4, <4>jn, <2>t DEF TypeOK
              <8>1. A'[q] = A[q]  BY <6>dom, <7>4, <4>e3
              <8>2. A[j] =< A[q]
                BY <8>0, <4>jn, <3>inv DEF IsSortedFromTo
              <8> QED BY <7>1, <8>1, <8>2
            <7> QED BY <7>2, <7>3, <7>4
          <6>2. CASE p = j
            <7>1. A'[p] = A[j - 1]  BY <6>2, <4>e2
            <7>2. CASE q = j
              <8>1. A'[q] = A[j - 1]  BY <7>2, <4>e2
              <8> QED BY <7>1, <8>1, <4>aint
            <7>3. CASE q # j
              <8>0. q \in (j + 1)..(i + 1)  BY <6>2, <7>3, <4>jn, <2>t DEF TypeOK
              <8>1. q # j - 1  BY <6>2, <7>3, <4>jn, <2>t DEF TypeOK
              <8>2. A'[q] = A[q]  BY <6>dom, <7>3, <8>1, <4>e3
              <8>3. A[j - 1] =< A[q]  BY <8>0, <4>jm1b, <3>inv
              <8> QED BY <7>1, <8>2, <8>3
            <7> QED BY <7>2, <7>3
          <6>3. CASE p # j - 1 /\ p # j
            <7>0. p \in (j + 1)..(i + 1)  BY <6>3, <4>jn, <2>t DEF TypeOK
            <7>1. A'[p] = A[p]  BY <6>dom, <6>3, <4>e3
            <7>2. q # j - 1 /\ q # j  BY <7>0, <4>jn, <2>t DEF TypeOK
            <7>3. A'[q] = A[q]  BY <6>dom, <7>2, <4>e3
            <7>4. p \in j..(i + 1) /\ q \in j..(i + 1)  BY <7>0, <4>jn, <2>t DEF TypeOK
            <7>5. A[p] =< A[q]  BY <7>4, <3>inv DEF IsSortedFromTo
            <7> QED BY <7>1, <7>3, <7>5
          <6> QED BY <6>1, <6>2, <6>3
        <5>c5. \A p \in 1..(j' - 1), q \in (j' + 1)..(i' + 1) : A'[p] =< A'[q]
          <6> TAKE p \in 1..(j' - 1), q \in (j' + 1)..(i' + 1)
          <6>p. /\ p \in 1..N /\ p # j - 1 /\ p # j /\ p \in 1..(j - 1)
            BY <4>def, <4>jn
          <6>pa. A'[p] = A[p]  BY <6>p, <4>e3
          <6>q. q \in 1..N /\ q >= j  BY <4>def, <3>inv, <4>jn, <2>t DEF TypeOK
          <6>1. CASE q = j
            <7>1. A'[q] = A[j - 1]  BY <6>1, <4>e2
            <7>2. A[p] =< A[j - 1]  BY <6>p, <3>inv DEF IsSortedTo
            <7> QED BY <6>pa, <7>1, <7>2
          <6>2. CASE q # j
            <7>0. q \in (j + 1)..(i + 1)  BY <6>q, <6>2, <4>def, <4>jn, <2>t DEF TypeOK
            <7>1. q # j - 1  BY <6>q, <4>jn, <2>t DEF TypeOK
            <7>2. A'[q] = A[q]  BY <6>q, <7>1, <6>2, <4>e3
            <7>3. A[p] =< A[q]  BY <6>p, <7>0, <3>inv
            <7> QED BY <6>pa, <7>2, <7>3
          <6> QED BY <6>1, <6>2
        <5>c6. IsPermOf(A', A0')
          <6>1. A' = A ** Exchange(j - 1, j)
            BY <4>def, <4>jm1, <4>jn, <4>jne, <2>t, SwapIsCompose DEF TypeOK
          <6>2. Exchange(j - 1, j) \in [1..N -> 1..N]
            BY <4>jm1, <4>jn, ExchangeInPerms
          <6>3. IsPermOf(A ** Exchange(j - 1, j), A0)
            BY <3>inv, <6>2, <2>t, PermCompose DEF TypeOK
          <6> QED BY <6>1, <6>3, <3>a0
        <5> QED BY <5>a, <5>c1, <5>c2, <5>c3, <5>c4, <5>c5, <5>c6 DEF RealInv
      <4> QED BY <4>tok, <4>ri DEF Inv
    <3>2. CASE ~(j > 1 /\ A[j-1] > A[j])
      <4>def. i' = i + 1 /\ pc' = "Lbl_1" /\ A' = A /\ j' = j
        BY <3>2
      <4>tok. TypeOK'
        BY <4>def, <3>inv, <2>t, <3>a0 DEF TypeOK
      <4>ri. RealInv'
        <5>a. pc' = "Lbl_1"  BY <4>def
        <5>b. IsSortedTo(A', i') /\ IsPermOf(A', A0')
          <6>1. IsSortedTo(A, i + 1)
            <7> SUFFICES \A p, q \in 1..(i + 1) : (p =< q) => A[p] =< A[q]
              BY DEF IsSortedTo
            <7> TAKE p, q \in 1..(i + 1)
            <7> HAVE p =< q
            <7>dom. p \in 1..N /\ q \in 1..N  BY <3>inv, <2>t DEF TypeOK
            <7>1. CASE j = 1
              BY <7>1, <3>inv DEF IsSortedFromTo
            <7>2. CASE j > 1
              <8>jm1. j - 1 \in 1..N  BY <7>2, <2>t DEF TypeOK
              <8>int. A[j - 1] \in Int /\ A[j] \in Int
                BY <8>jm1, <2>t DEF TypeOK
              <8>0. A[j - 1] =< A[j]  BY <7>2, <3>2, <8>int
              <8>1. CASE p \in 1..(j - 1) /\ q \in 1..(j - 1)
                BY <8>1, <3>inv DEF IsSortedTo
              <8>2. CASE p \in j..(i + 1) /\ q \in j..(i + 1)
                BY <8>2, <3>inv DEF IsSortedFromTo
              <8>3. CASE p \in 1..(j - 1) /\ q \in j..(i + 1)
                <9>1. CASE q = j
                  <10>1. A[p] =< A[j - 1]  BY <8>3, <3>inv DEF IsSortedTo
                  <10>2. A[j - 1] \in Int /\ A[j] \in Int /\ A[p] \in Int
                    BY <8>3, <7>dom, <7>2, <2>t DEF TypeOK
                  <10> QED BY <10>1, <8>0, <9>1, <10>2
                <9>2. CASE q # j
                  <10>1. q \in (j + 1)..(i + 1)  BY <8>3, <9>2, <7>2, <2>t DEF TypeOK
                  <10> QED BY <8>3, <10>1, <3>inv
                <9> QED BY <9>1, <9>2
              <8>4. CASE p \in j..(i + 1) /\ q \in 1..(j - 1)
                BY <8>4, <7>2, <2>t DEF TypeOK
              <8> QED BY <8>1, <8>2, <8>3, <8>4, <3>inv, <7>2, <2>t DEF TypeOK
            <7> QED BY <7>1, <7>2, <2>t DEF TypeOK
          <6>2. IsPermOf(A', A0')  BY <4>def, <3>inv, <3>a0
          <6> QED BY <6>1, <6>2, <4>def
        <5> QED BY <5>a, <5>b DEF RealInv
      <4> QED BY <4>tok, <4>ri DEF Inv
    <3> QED BY <3>1, <3>2
  <2>3. CASE vars' = vars
    <3> A' = A /\ A0' = A0 /\ i' = i /\ j' = j /\ pc' = pc
      BY <2>3 DEF vars
    <3> QED BY <2>t DEF Inv, TypeOK, RealInv
  <2> QED BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => (pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
  BY DEF Inv, RealInv
<1> QED
  <2>1. Spec => []Inv
    BY <1>1, <1>2, PTL DEF Spec
  <2> QED BY <2>1, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Except for writing the comments, writing this module, including         *)
(* checking the proofs, took about 6.5 hours.                              *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Mon Mar 17 11:17:49 CET 2014 by doligez
\* Last modified Fri Mar 07 15:24:43 CET 2014 by shaolin
\* Last modified Tue Nov 27 13:33:10 CET 2012 by doligez
\* Last modified Fri Nov 23 09:32:08 PST 2012 by lamport
\* Created Wed Nov 21 11:50:58 PST 2012 by lamport
