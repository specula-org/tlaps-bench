----------------------------- MODULE BubbleSort_line202 -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

-----------------------------------------------------------------------------

IsSortedTo(A, i) == \A j, k \in 1..i : (j =< k) => (A[j] =< A[k])

IsSorted(A) == IsSortedTo(A, N)

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

----------------------------------------------------------------------------

VARIABLES A, A0, i, j, pc

vars == << A, A0, i, j, pc >>

Init == 
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
           \/ 
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

-----------------------------------------------------------------------------

SortedRange(arr, lo, hi) == \A p, q \in lo..hi : (p <= q) => (arr[p] <= arr[q])

TypeOK ==
  /\ A  \in [1..N -> Int]
  /\ A0 \in [1..N -> Int]
  /\ i  \in 1..N
  /\ j  \in 1..N
  /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

InnerInv ==
  /\ i < N
  /\ j \in 1..(i+1)
  /\ SortedRange(A, 1, j-1)
  /\ SortedRange(A, j, i+1)
  /\ (j > 1 /\ j < i+1) => (A[j-1] <= A[j+1])

Inv ==
  /\ TypeOK
  /\ IsPermOf(A, A0)
  /\ (pc = "Lbl_1") => SortedRange(A, 1, i)
  /\ (pc = "Lbl_2") => InnerInv
  /\ (pc = "Done")  => SortedRange(A, 1, N)

LEMMA SortedSubRange ==
  ASSUME NEW arr, NEW lo \in Int, NEW hi \in Int,
         NEW lo2 \in Int, NEW hi2 \in Int,
         lo <= lo2, hi2 <= hi, SortedRange(arr, lo, hi)
  PROVE  SortedRange(arr, lo2, hi2)
PROOF
  <1> SUFFICES ASSUME NEW p \in lo2..hi2, NEW q \in lo2..hi2, p <= q
               PROVE  arr[p] <= arr[q]
    BY DEF SortedRange
  <1>1. p \in lo..hi /\ q \in lo..hi
    OBVIOUS
  <1> QED BY <1>1 DEF SortedRange

LEMMA SortedRangeCong ==
  ASSUME NEW arr, NEW brr, NEW lo \in Int, NEW hi \in Int,
         \A k \in lo..hi : arr[k] = brr[k],
         SortedRange(arr, lo, hi)
  PROVE  SortedRange(brr, lo, hi)
PROOF
  <1> SUFFICES ASSUME NEW p \in lo..hi, NEW q \in lo..hi, p <= q
               PROVE  brr[p] <= brr[q]
    BY DEF SortedRange
  <1>1. brr[p] = arr[p] /\ brr[q] = arr[q]
    OBVIOUS
  <1>2. arr[p] <= arr[q]
    BY DEF SortedRange
  <1> QED BY <1>1, <1>2

LEMMA SortedAdjacent ==
  ASSUME NEW arr \in [1..N -> Int],
         NEW a \in 1..N, NEW c \in 1..N, NEW m \in Int,
         a <= m, m+1 <= c,
         SortedRange(arr, a, m),
         SortedRange(arr, m+1, c),
         arr[m] <= arr[m+1]
  PROVE  SortedRange(arr, a, c)
PROOF
  <1> SUFFICES ASSUME NEW p \in a..c, NEW q \in a..c, p <= q
               PROVE  arr[p] <= arr[q]
    BY DEF SortedRange
  <1>m. m \in 1..N /\ (m+1) \in 1..N
    BY NAssumption
  <1>1. CASE q <= m
    <2>1. p \in a..m /\ q \in a..m  BY <1>1
    <2> QED BY <2>1 DEF SortedRange
  <1>2. CASE m+1 <= p
    <2>1. p \in (m+1)..c /\ q \in (m+1)..c  BY <1>2
    <2> QED BY <2>1 DEF SortedRange
  <1>3. CASE p <= m /\ m+1 <= q
    <2>1. p \in a..m /\ m \in a..m  BY <1>3
    <2>2. arr[p] <= arr[m]  BY <2>1, <1>3 DEF SortedRange
    <2>3. (m+1) \in (m+1)..c /\ q \in (m+1)..c  BY <1>3
    <2>4. arr[m+1] <= arr[q]  BY <2>3, <1>3 DEF SortedRange
    <2>5. p \in 1..N /\ q \in 1..N  BY NAssumption
    <2>6. arr[p] \in Int /\ arr[q] \in Int /\ arr[m] \in Int /\ arr[m+1] \in Int
      BY <2>5, <1>m
    <2> QED BY <2>2, <2>4, <2>6
  <1> QED BY <1>1, <1>2, <1>3

LEMMA SwapType ==
  ASSUME NEW S, NEW f \in [1..N -> S], NEW x \in 1..N, NEW y \in 1..N, x # y
  PROVE  /\ [f EXCEPT ![x] = f[y], ![y] = f[x]] \in [1..N -> S]
         /\ [f EXCEPT ![x] = f[y], ![y] = f[x]][x] = f[y]
         /\ [f EXCEPT ![x] = f[y], ![y] = f[x]][y] = f[x]
         /\ \A k \in 1..N : (k # x /\ k # y) =>
              [f EXCEPT ![x] = f[y], ![y] = f[x]][k] = f[k]
PROOF
  <1>1. f[x] \in S /\ f[y] \in S  OBVIOUS
  <1>2. [f EXCEPT ![x] = f[y], ![y] = f[x]] \in [1..N -> S]  BY <1>1
  <1>3. [f EXCEPT ![x] = f[y], ![y] = f[x]][x] = f[y]  BY <1>1
  <1>4. [f EXCEPT ![x] = f[y], ![y] = f[x]][y] = f[x]  BY <1>1
  <1>5. \A k \in 1..N : (k # x /\ k # y) =>
              [f EXCEPT ![x] = f[y], ![y] = f[x]][k] = f[k]  BY <1>1
  <1> QED BY <1>2, <1>3, <1>4, <1>5

LEMMA PermSwap ==
  ASSUME NEW B \in [1..N -> Int], NEW C \in [1..N -> Int],
         IsPermOf(B, C),
         NEW x \in 1..N, NEW y \in 1..N, x # y
  PROVE  IsPermOf([B EXCEPT ![x] = B[y], ![y] = B[x]], C)
PROOF
  <1>1. PICK f \in Perms : B = C ** f
    BY DEF IsPermOf
  <1>2. f \in [1..N -> 1..N]
    BY <1>1 DEF Perms
  <1> DEFINE g  == [f EXCEPT ![x] = f[y], ![y] = f[x]]
  <1> DEFINE Bp == [B EXCEPT ![x] = B[y], ![y] = B[x]]
  <1>swB. /\ Bp \in [1..N -> Int]
          /\ Bp[x] = B[y]
          /\ Bp[y] = B[x]
          /\ \A k \in 1..N : (k # x /\ k # y) => Bp[k] = B[k]
    BY SwapType
  <1>swg. /\ g \in [1..N -> 1..N]
          /\ g[x] = f[y]
          /\ g[y] = f[x]
          /\ \A k \in 1..N : (k # x /\ k # y) => g[k] = f[k]
    BY <1>2, SwapType
  <1>3. g \in Perms
    BY <1>swg DEF Perms
  <1>4. C ** g = [k \in 1..N |-> C[g[k]]]
    BY DEF **
  <1>1b. \A k \in 1..N : B[k] = C[f[k]]
    <2> SUFFICES ASSUME NEW k \in 1..N PROVE B[k] = C[f[k]]
      OBVIOUS
    <2>1. (C ** f)[k] = C[f[k]]
      BY <1>2 DEF **
    <2> QED BY <1>1, <2>1
  <1>7. \A k \in 1..N : Bp[k] = C[g[k]]
    <2> SUFFICES ASSUME NEW k \in 1..N PROVE Bp[k] = C[g[k]]
      OBVIOUS
    <2>b. CASE k = x
      <3>1. Bp[k] = B[y]  BY <2>b, <1>swB
      <3>2. g[k] = f[y]   BY <2>b, <1>swg
      <3>3. B[y] = C[f[y]]  BY <1>1b
      <3> QED BY <3>1, <3>2, <3>3
    <2>c. CASE k = y
      <3>1. Bp[k] = B[x]  BY <2>c, <1>swB
      <3>2. g[k] = f[x]   BY <2>c, <1>swg
      <3>3. B[x] = C[f[x]]  BY <1>1b
      <3> QED BY <3>1, <3>2, <3>3
    <2>d. CASE k # x /\ k # y
      <3>1. Bp[k] = B[k]  BY <2>d, <1>swB
      <3>2. g[k] = f[k]   BY <2>d, <1>swg
      <3>3. B[k] = C[f[k]]  BY <1>1b
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>b, <2>c, <2>d
  <1>8. Bp = C ** g
    <2>1. Bp = [k \in 1..N |-> Bp[k]]
      BY <1>swB
    <2>2. C ** g = [k \in 1..N |-> Bp[k]]
      <3>1. \A k \in 1..N : C[g[k]] = Bp[k]
        BY <1>7
      <3> QED BY <1>4, <3>1
    <2> QED BY <2>1, <2>2
  <1> QED
    BY <1>3, <1>8 DEF IsPermOf

LEMMA InitInv == Init => Inv
PROOF
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeOK
    BY NAssumption DEF Init, TypeOK
  <1>2. IsPermOf(A, A0)
    <2> DEFINE id == [k \in 1..N |-> k]
    <2>1. id \in Perms
      BY DEF Perms
    <2>2. A ** id = A
      <3>1. A ** id = [k \in 1..N |-> A[id[k]]]
        BY DEF **
      <3>2. \A k \in 1..N : A[id[k]] = A[k]
        OBVIOUS
      <3>3. A = [k \in 1..N |-> A[k]]
        BY DEF Init
      <3> QED BY <3>1, <3>2, <3>3
    <2>3. A = A0 ** id
      BY <2>2 DEF Init
    <2> QED BY <2>1, <2>3 DEF IsPermOf
  <1>3. (pc = "Lbl_1") => SortedRange(A, 1, i)
    BY NAssumption DEF Init, SortedRange
  <1>4. (pc = "Lbl_2") => InnerInv
    BY DEF Init
  <1>5. (pc = "Done") => SortedRange(A, 1, N)
    BY DEF Init
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
PROOF
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE NAssumption
  <1>T. TypeOK  BY DEF Inv
  <1>P. IsPermOf(A, A0)  BY DEF Inv
  (***********************************************************************)
  (* CASE Lbl_1                                                          *)
  (***********************************************************************)
  <1>1. CASE Lbl_1
    <2> USE <1>1 DEF Lbl_1
    <2>U. A' = A /\ A0' = A0 /\ i' = i
      BY DEF Lbl_1
    <2>1. TypeOK'
      <3>1. A' \in [1..N -> Int]  BY <2>U, <1>T DEF TypeOK
      <3>2. A0' \in [1..N -> Int]  BY <2>U, <1>T DEF TypeOK
      <3>3. i' \in 1..N  BY <2>U, <1>T DEF TypeOK
      <3>4. j' \in 1..N
        <4>1. CASE i < N
          BY <4>1, <1>T DEF TypeOK
        <4>2. CASE ~(i < N)
          BY <4>2, <1>T DEF TypeOK
        <4> QED BY <4>1, <4>2
      <3>5. pc' \in {"Lbl_1", "Lbl_2", "Done"}
        <4>1. CASE i < N
          BY <4>1
        <4>2. CASE ~(i < N)
          BY <4>2
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF TypeOK
    <2>2. IsPermOf(A', A0')
      BY <2>U, <1>P
    <2>3. (pc' = "Lbl_1") => SortedRange(A', 1, i')
      <3>1. pc' # "Lbl_1"
        OBVIOUS
      <3> QED BY <3>1
    <2>4. (pc' = "Lbl_2") => InnerInv'
      <3> SUFFICES ASSUME pc' = "Lbl_2" PROVE InnerInv'
        OBVIOUS
      <3>1. i < N
        OBVIOUS
      <3>2. j' = i+1 /\ i' = i /\ A' = A
        BY <3>1, <2>U
      <3>3. i' < N  BY <3>1, <3>2
      <3>4. j' \in 1..(i'+1)
        BY <3>2, <1>T DEF TypeOK
      <3>5. SortedRange(A', 1, j'-1)
        <4>1. SortedRange(A, 1, i)  BY DEF Inv
        <4>2. j' - 1 = i  BY <3>2, <1>T DEF TypeOK
        <4> QED BY <4>1, <4>2, <3>2
      <3>6. SortedRange(A', j', i'+1)
        <4>0. A' = A /\ j' = i+1 /\ i'+1 = i+1  BY <3>2
        <4>1. (i+1) \in 1..N  BY <3>1, <1>T DEF TypeOK
        <4>2. A[i+1] \in Int  BY <4>1, <1>T DEF TypeOK
        <4>3. SortedRange(A, i+1, i+1)  BY <4>1, <4>2 DEF SortedRange
        <4> QED BY <4>0, <4>3
      <3>7. (j' > 1 /\ j' < i'+1) => (A'[j'-1] <= A'[j'+1])
        BY <3>2
      <3> QED BY <3>3, <3>4, <3>5, <3>6, <3>7 DEF InnerInv
    <2>5. (pc' = "Done") => SortedRange(A', 1, N)
      <3> SUFFICES ASSUME pc' = "Done" PROVE SortedRange(A', 1, N)
        OBVIOUS
      <3>1. ~(i < N)
        OBVIOUS
      <3>2. i = N
        BY <3>1, <1>T DEF TypeOK
      <3>3. SortedRange(A, 1, i)  BY DEF Inv
      <3> QED BY <2>U, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Inv
  (***********************************************************************)
  (* CASE Lbl_2                                                          *)
  (***********************************************************************)
  <1>2. CASE Lbl_2
    <2> USE <1>2 DEF Lbl_2
    <2>0. pc = "Lbl_2"  BY DEF Lbl_2
    <2>I. InnerInv  BY <2>0 DEF Inv
    <2>i1. i < N  BY <2>I DEF InnerInv
    <2>i2. j \in 1..(i+1)  BY <2>I DEF InnerInv
    <2>i3. SortedRange(A, 1, j-1)  BY <2>I DEF InnerInv
    <2>i4. SortedRange(A, j, i+1)  BY <2>I DEF InnerInv
    <2>i5. (j > 1 /\ j < i+1) => (A[j-1] <= A[j+1])  BY <2>I DEF InnerInv
    <2>A0. A0' = A0  BY DEF Lbl_2
    <2>n. i+1 <= N /\ i \in 1..N /\ j \in 1..N
      BY <2>i1, <2>i2, <1>T DEF TypeOK
    (*--------------------- THEN branch: swap ---------------------*)
    <2>T1. CASE j > 1 /\ A[j-1] > A[j]
      <3>jm1. (j-1) \in 1..N /\ j-1 # j
        BY <2>T1, <2>n
      <3>A1. A' = [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]]
        BY <2>T1
      <3>sw0. /\ [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]] \in [1..N -> Int]
              /\ [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]][j-1] = A[j]
              /\ [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]][j] = A[j-1]
              /\ \A k \in 1..N : (k # j-1 /\ k # j) =>
                   [A EXCEPT ![j-1] = A[j], ![j] = A[j-1]][k] = A[k]
        BY <3>jm1, <2>n, <1>T, SwapType DEF TypeOK
      <3>sw. /\ A' \in [1..N -> Int]
             /\ A'[j-1] = A[j]
             /\ A'[j] = A[j-1]
             /\ \A k \in 1..N : (k # j-1 /\ k # j) => A'[k] = A[k]
        BY <3>A1, <3>sw0
      <3>0. i' = i /\ j' = j-1 /\ pc' = "Lbl_2"
        BY <2>T1
      <3>1. TypeOK'
        <4>1. A' \in [1..N -> Int]  BY <3>sw
        <4>2. A0' \in [1..N -> Int]  BY <2>A0, <1>T DEF TypeOK
        <4>3. i' \in 1..N  BY <3>0, <2>n
        <4>4. j' \in 1..N  BY <3>0, <3>jm1
        <4>5. pc' \in {"Lbl_1", "Lbl_2", "Done"}  BY <3>0
        <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK
      <3>2. IsPermOf(A', A0')
        <4>0. IsPermOf([A EXCEPT ![j-1] = A[j], ![j] = A[j-1]], A0)
          BY <1>P, <3>jm1, <2>n, <1>T, PermSwap DEF TypeOK
        <4>1. IsPermOf(A', A0)  BY <4>0, <3>A1
        <4> QED BY <4>1, <2>A0
      <3>3. (pc' = "Lbl_1") => SortedRange(A', 1, i')
        BY <3>0
      <3>4. InnerInv'
        <4>1. i' < N  BY <3>0, <2>i1
        <4>2. j' \in 1..(i'+1)  BY <3>0, <2>T1, <2>i2, <2>n
        <4>3. SortedRange(A', 1, j'-1)
          <5>1. SortedRange(A, 1, j-2)
            BY <2>i3, <3>jm1, <2>n, SortedSubRange
          <5>2. \A k \in 1..(j-2) : A'[k] = A[k]
            <6> SUFFICES ASSUME NEW k \in 1..(j-2) PROVE A'[k] = A[k]
              OBVIOUS
            <6>1. k \in 1..N /\ k # j-1 /\ k # j
              BY <2>n, <3>jm1
            <6> QED BY <6>1, <3>sw
          <5>3. j'-1 = j-2  BY <3>0, <2>n
          <5> QED BY <5>1, <5>2, <5>3, <3>jm1, <2>n, SortedRangeCong
        <4>4. SortedRange(A', j', i'+1)
          <5>g. j' = j-1 /\ i'+1 = i+1  BY <3>0
          <5>A. SortedRange(A', j, i+1)
            <6>1. CASE j = i+1
              <7>1. A'[i+1] \in Int
                BY <2>n, <3>sw
              <7>2. SortedRange(A', i+1, i+1)  BY <7>1, <2>n DEF SortedRange
              <7> QED BY <6>1, <7>2
            <6>2. CASE j < i+1
              <7>1. SortedRange(A', j, j)
                <8>1. A'[j] \in Int  BY <2>n, <3>sw
                <8> QED BY <8>1, <2>n DEF SortedRange
              <7>2. SortedRange(A, j+1, i+1)
                BY <2>i4, <2>n, SortedSubRange
              <7>3. \A k \in (j+1)..(i+1) : A'[k] = A[k]
                <8> SUFFICES ASSUME NEW k \in (j+1)..(i+1) PROVE A'[k] = A[k]
                  OBVIOUS
                <8>1. k \in 1..N /\ k # j-1 /\ k # j
                  BY <2>n, <6>2
                <8> QED BY <8>1, <3>sw
              <7>4. SortedRange(A', j+1, i+1)
                BY <7>2, <7>3, <2>n, <6>2, SortedRangeCong
              <7>5. A'[j] <= A'[j+1]
                <8>1. A'[j] = A[j-1]  BY <3>sw
                <8>2. A'[j+1] = A[j+1]
                  <9>1. (j+1) \in 1..N /\ j+1 # j-1 /\ j+1 # j  BY <2>n, <6>2
                  <9> QED BY <9>1, <3>sw
                <8>3. A[j-1] <= A[j+1]  BY <2>i5, <2>T1, <6>2
                <8> QED BY <8>1, <8>2, <8>3
              <7>6. SortedRange(A', j, i+1)
                BY <7>1, <7>4, <7>5, <2>n, <2>i2, <6>2, <3>sw, SortedAdjacent
              <7> QED BY <7>6
            <6> QED BY <6>1, <6>2, <2>i2, <2>n
          <5>B1. SortedRange(A', j-1, j-1)
            <6>1. A'[j-1] \in Int  BY <3>jm1, <3>sw
            <6> QED BY <6>1, <3>jm1 DEF SortedRange
          <5>B2. A'[j-1] <= A'[j]
            <6>1. A'[j-1] = A[j]  BY <3>sw
            <6>2. A'[j] = A[j-1]  BY <3>sw
            <6>3. A[j] <= A[j-1]  BY <2>T1
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED
            BY <5>A, <5>B1, <5>B2, <5>g, <3>jm1, <2>n, <2>i2, <3>sw, SortedAdjacent
        <4>5. (j' > 1 /\ j' < i'+1) => (A'[j'-1] <= A'[j'+1])
          <5> SUFFICES ASSUME j' > 1 /\ j' < i'+1 PROVE A'[j'-1] <= A'[j'+1]
            OBVIOUS
          <5>1. j > 2  BY <3>0, <2>n
          <5>2. A'[j'-1] = A[j-2]
            <6>1. (j-2) \in 1..N /\ j-2 # j-1 /\ j-2 # j  BY <5>1, <2>n
            <6>2. j'-1 = j-2  BY <3>0, <2>n
            <6> QED BY <6>1, <6>2, <3>sw
          <5>3. A'[j'+1] = A[j-1]
            <6>1. j'+1 = j  BY <3>0, <2>n
            <6> QED BY <6>1, <3>sw
          <5>4. A[j-2] <= A[j-1]
            <6>1. (j-2) \in 1..(j-1) /\ (j-1) \in 1..(j-1)  BY <5>1, <2>n
            <6> QED BY <6>1, <2>i3, <5>1 DEF SortedRange
          <5> QED BY <5>2, <5>3, <5>4
        <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF InnerInv
      <3>4b. (pc' = "Lbl_2") => InnerInv'  BY <3>4
      <3>5. (pc' = "Done") => SortedRange(A', 1, N)
        BY <3>0
      <3> QED BY <3>1, <3>2, <3>3, <3>4b, <3>5 DEF Inv
    (*--------------------- ELSE branch: advance i ---------------------*)
    <2>T2. CASE ~(j > 1 /\ A[j-1] > A[j])
      <3>0. i' = i+1 /\ pc' = "Lbl_1" /\ A' = A /\ j' = j
        BY <2>T2
      <3>1. TypeOK'
        <4>1. A' \in [1..N -> Int]  BY <3>0, <1>T DEF TypeOK
        <4>2. A0' \in [1..N -> Int]  BY <2>A0, <1>T DEF TypeOK
        <4>3. i' \in 1..N  BY <3>0, <2>n
        <4>4. j' \in 1..N  BY <3>0, <2>n
        <4>5. pc' \in {"Lbl_1", "Lbl_2", "Done"}  BY <3>0
        <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK
      <3>2. IsPermOf(A', A0')  BY <3>0, <2>A0, <1>P
      <3>3. (pc' = "Lbl_1") => SortedRange(A', 1, i')
        <4> SUFFICES SortedRange(A', 1, i')
          BY <3>0
        <4>g. A' = A /\ i' = i+1  BY <3>0
        <4>1. CASE j = 1
          BY <4>1, <4>g, <2>i4
        <4>2. CASE j > 1
          <5>0. (j-1) \in 1..N /\ 1 \in 1..N /\ (i+1) \in 1..N
            BY <4>2, <2>n
          <5>1. A[j-1] <= A[j]  BY <2>T2, <4>2, <5>0, <2>n, <1>T DEF TypeOK
          <5>2. SortedRange(A, 1, i+1)
            BY <2>i3, <2>i4, <5>1, <5>0, <2>i2, <4>2, <1>T, SortedAdjacent DEF TypeOK
          <5> QED BY <5>2, <4>g
        <4> QED BY <4>1, <4>2, <2>n
      <3>4. (pc' = "Lbl_2") => InnerInv'
        BY <3>0
      <3>5. (pc' = "Done") => SortedRange(A', 1, N)
        BY <3>0
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2> QED BY <2>T1, <2>T2
  (***********************************************************************)
  (* CASE stuttering                                                     *)
  (***********************************************************************)
  <1>3. CASE UNCHANGED vars
    <2>1. A' = A /\ A0' = A0 /\ i' = i /\ j' = j /\ pc' = pc
      BY <1>3 DEF vars
    <2>2. TypeOK'
      BY <2>1, <1>T DEF TypeOK
    <2>3. IsPermOf(A', A0')  BY <2>1, <1>P
    <2>4. (pc' = "Lbl_1") => SortedRange(A', 1, i')
      BY <2>1 DEF Inv
    <2>5. (pc' = "Lbl_2") => InnerInv'
      BY <2>1 DEF Inv, InnerInv
    <2>6. (pc' = "Done") => SortedRange(A', 1, N)
      BY <2>1 DEF Inv
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1> QED BY <1>1, <1>2, <1>3 DEF Next

-----------------------------------------------------------------------------

THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
PROOF
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1>3. Inv => (pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
    <2> SUFFICES ASSUME Inv, pc = "Done"
                 PROVE  IsSorted(A) /\ IsPermOf(A, A0)
      OBVIOUS
    <2>1. IsPermOf(A, A0)  BY DEF Inv
    <2>2. SortedRange(A, 1, N)  BY DEF Inv
    <2>3. IsSorted(A)  BY <2>2 DEF IsSorted, IsSortedTo, SortedRange
    <2> QED BY <2>1, <2>3
  <1>4. Spec => []Inv
    BY <1>1, <1>2, PTL DEF Spec
  <1> QED
    <2>1. []Inv => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
      BY <1>3, PTL
    <2> QED BY <1>4, <2>1

-----------------------------------------------------------------------------

=============================================================================

