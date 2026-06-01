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

SwapIdx(f, q) ==
        [k \in 1..N |->
           IF k = q-1 THEN f[q]
           ELSE IF k = q THEN f[q-1]
           ELSE f[k]]
   
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

RangeSorted(B, lo, hi) ==
        \A x, y \in lo..hi : (x =< y) => (B[x] =< B[y])

InsertInv(B, p, q) ==
        \A x, y \in 1..(p+1) : (x =< y /\ y # q) => (B[x] =< B[y])

TypeInv ==
        /\ A \in [1..N -> Int]
        /\ A0 \in [1..N -> Int]
        /\ i \in 1..N
        /\ j \in 1..N
        /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

OrderInv ==
        /\ pc = "Lbl_1" => IsSortedTo(A, i)
        /\ pc = "Lbl_2" => /\ i \in 1..(N-1)
                            /\ j \in 1..(i+1)
                            /\ InsertInv(A, i, j)
        /\ pc = "Done" => /\ i = N
                           /\ IsSorted(A)

PermInv == IsPermOf(A, A0)

IndInv == TypeInv /\ OrderInv /\ PermInv

LEMMA PermsAll ==
        \A f \in [1..N -> 1..N] : f \in Perms
BY NAssumption DEF Perms

LEMMA InitPerm ==
        ASSUME A \in [1..N -> Int],
               A0 = A
        PROVE  IsPermOf(A, A0)
<1>1. [k \in 1..N |-> k] \in [1..N -> 1..N]
  BY NAssumption, SMT
<1>2. [k \in 1..N |-> k] \in Perms
  BY <1>1, PermsAll
<1>3. A = (A0 ** [k \in 1..N |-> k])
  BY <1>1, NAssumption DEF **
<1>. QED
  BY <1>2, <1>3 DEF IsPermOf

LEMMA PermStepUnchanged ==
        ASSUME IsPermOf(A, A0),
               A' = A,
               A0' = A0
        PROVE  IsPermOf(A', A0')
BY DEF IsPermOf

LEMMA SwapCompose ==
        ASSUME A \in [1..N -> Int],
               A0 \in [1..N -> Int],
               j \in 2..N,
               NEW f \in [1..N -> 1..N],
               A = (A0 ** f),
               A' = [A EXCEPT ![j-1] = A[j],
                              ![j] = A[j-1]],
               A0' = A0
        PROVE  A' = (A0' ** SwapIdx(f, j))
<1>1. SwapIdx(f, j) \in [1..N -> 1..N]
  BY NAssumption, SMT DEF SwapIdx
<1>2. A' \in [1..N -> Int]
  BY NAssumption, SMT
<1>3. (A0' ** SwapIdx(f, j)) \in [1..N -> Int]
  BY <1>1, NAssumption, SMT DEF **
<1>4. \A k \in 1..N : A'[k] = (A0' ** SwapIdx(f, j))[k]
  <2>. SUFFICES ASSUME NEW k \in 1..N
                  PROVE  A'[k] = (A0' ** SwapIdx(f, j))[k]
    OBVIOUS
  <2>1. CASE k = j-1
    BY <2>1, NAssumption, SMT DEF SwapIdx, **
  <2>2. CASE k = j
    BY <2>2, NAssumption, SMT DEF SwapIdx, **
  <2>3. CASE k # j-1 /\ k # j
    BY <2>3, NAssumption, SMT DEF SwapIdx, **
  <2>. QED
    BY <2>1, <2>2, <2>3, SMT
<1>. QED
  BY <1>2, <1>3, <1>4

LEMMA SwapPerm ==
        ASSUME A \in [1..N -> Int],
               A0 \in [1..N -> Int],
               j \in 2..N,
               IsPermOf(A, A0),
               A' = [A EXCEPT ![j-1] = A[j],
                              ![j] = A[j-1]],
               A0' = A0
        PROVE  IsPermOf(A', A0')
<1>1. PICK f \in Perms : A = (A0 ** f)
  BY DEF IsPermOf
<1>2. f \in [1..N -> 1..N]
  BY <1>1, NAssumption DEF Perms
<1>3. SwapIdx(f, j) \in [1..N -> 1..N]
  BY <1>2, NAssumption, SMT DEF SwapIdx
<1>4. A' = (A0' ** SwapIdx(f, j))
  BY <1>1, <1>2, SwapCompose
<1>. QED
  BY <1>3, <1>4, PermsAll DEF IsPermOf

LEMMA SortedOne ==
        ASSUME NEW B \in [1..N -> Int],
               NEW n \in 1..N
        PROVE  IsSortedTo(B, 1)
BY NAssumption, SMT DEF IsSortedTo

LEMMA SortedPrefixStartsInsert ==
        ASSUME NEW B,
               NEW p \in 1..(N-1),
               IsSortedTo(B, p)
        PROVE  InsertInv(B, p, p+1)
BY NAssumption, SMT DEF IsSortedTo, InsertInv

LEMMA InsertSwapPreserves ==
        ASSUME NEW B \in [1..N -> Int],
               NEW p \in 1..(N-1),
               NEW q \in 2..(p+1),
               InsertInv(B, p, q),
               B[q-1] > B[q],
               NEW C,
               C = [B EXCEPT ![q-1] = B[q],
                             ![q] = B[q-1]]
        PROVE  InsertInv(C, p, q-1)
BY NAssumption, SMT DEF InsertInv

LEMMA InsertDoneSorted ==
        ASSUME NEW B \in [1..N -> Int],
               NEW p \in 1..(N-1),
               NEW q \in 1..(p+1),
               InsertInv(B, p, q),
               ~(q > 1 /\ B[q-1] > B[q])
        PROVE  IsSortedTo(B, p+1)
<1>. SUFFICES ASSUME NEW x \in 1..(p+1),
                     NEW y \in 1..(p+1),
                     x =< y
              PROVE  B[x] =< B[y]
  BY DEF IsSortedTo
<1>1. CASE y # q
  BY <1>1 DEF InsertInv
<1>2. CASE y = q
  <2>1. CASE x = q
    <3>1. B[x] = B[y]
      BY <1>2, <2>1
    <3>2. B[x] \in Int
      BY NAssumption, SMT
    <3>. QED
      BY <3>1, <3>2, SMT
  <2>2. CASE x # q
    <3>1. q > 1 /\ x =< q-1
      BY <1>2, <2>2, NAssumption, SMT
    <3>2. B[q-1] =< B[q]
      BY <3>1, NAssumption, SMT
    <3>3. B[x] =< B[q-1]
      BY <3>1, <2>2 DEF InsertInv
    <3>4. /\ B[x] \in Int
           /\ B[q-1] \in Int
           /\ B[q] \in Int
      BY <3>1, NAssumption, SMT
    <3>. QED
      BY <1>2, <3>2, <3>3, <3>4, SMT
  <2>. QED
    BY <2>1, <2>2
<1>. QED
  BY <1>1, <1>2

LEMMA InitIndInv == Init => IndInv
<1>. SUFFICES ASSUME Init
              PROVE  IndInv
  OBVIOUS
<1>1. TypeInv
  BY NAssumption, SMT DEF Init, TypeInv
<1>2. IsSortedTo(A, i)
  BY NAssumption, SMT DEF Init, IsSortedTo
<1>3. OrderInv
  BY <1>2, SMT DEF Init, OrderInv, IsSorted
<1>4. PermInv
  BY InitPerm DEF Init, PermInv
<1>. QED
  BY <1>1, <1>3, <1>4 DEF IndInv

LEMMA Lbl_1Inductive == IndInv /\ Lbl_1 => IndInv'
BY SortedPrefixStartsInsert, PermStepUnchanged, NAssumption, Isa
   DEF IndInv, TypeInv, OrderInv, PermInv, Lbl_1, IsSorted

LEMMA Lbl_2SwapInductive ==
        ASSUME IndInv,
               pc = "Lbl_2",
               j > 1 /\ A[j-1] > A[j],
               A' = [A EXCEPT ![j-1] = A[j],
                              ![j] = A[j-1]],
               j' = j-1,
               pc' = "Lbl_2",
               i' = i,
               A0' = A0
        PROVE  IndInv'
<1>1. TypeInv'
  BY NAssumption, SMT DEF IndInv, TypeInv, OrderInv
<1>2. /\ i' \in 1..(N-1)
       /\ j' \in 1..(i'+1)
       /\ InsertInv(A', i', j')
  BY InsertSwapPreserves, NAssumption, SMT
     DEF IndInv, TypeInv, OrderInv
<1>3. OrderInv'
  BY <1>2, SMT DEF OrderInv, IsSorted
<1>4. PermInv'
  BY SwapPerm DEF IndInv, TypeInv, PermInv, OrderInv
<1>. QED
  BY <1>1, <1>3, <1>4 DEF IndInv

LEMMA Lbl_2DoneInductive ==
        ASSUME IndInv,
               pc = "Lbl_2",
               ~(j > 1 /\ A[j-1] > A[j]),
               i' = i+1,
               pc' = "Lbl_1",
               A' = A,
               j' = j,
               A0' = A0
        PROVE  IndInv'
<1>1. TypeInv'
  BY NAssumption, SMT DEF IndInv, TypeInv, OrderInv
<1>2. IsSortedTo(A', i')
  BY InsertDoneSorted, NAssumption, SMT
     DEF IndInv, TypeInv, OrderInv
<1>3. OrderInv'
  BY <1>2, SMT DEF OrderInv, IsSorted
<1>4. PermInv'
  BY PermStepUnchanged DEF IndInv, PermInv
<1>. QED
  BY <1>1, <1>3, <1>4 DEF IndInv

LEMMA Lbl_2Inductive == IndInv /\ Lbl_2 => IndInv'
BY Lbl_2SwapInductive, Lbl_2DoneInductive, NAssumption, Isa
   DEF Lbl_2

LEMMA DoneInductive == IndInv /\ pc = "Done" /\ UNCHANGED vars => IndInv'
BY Isa DEF IndInv, TypeInv, OrderInv, PermInv, vars, IsSorted, IsPermOf

LEMMA StutterInductive == IndInv /\ UNCHANGED vars => IndInv'
BY Isa DEF IndInv, TypeInv, OrderInv, PermInv, vars, IsSorted, IsPermOf

LEMMA Inductive == IndInv /\ [Next]_vars => IndInv'
BY Lbl_1Inductive, Lbl_2Inductive, DoneInductive, StutterInductive, Isa
   DEF Next, vars

LEMMA IndInvImpliesGoal ==
        IndInv => (pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
BY DEF IndInv, OrderInv, PermInv

-----------------------------------------------------------------------------

THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
<1>1. Spec => []IndInv
  BY InitIndInv, Inductive, PTL DEF Spec
<1>. QED
  BY <1>1, IndInvImpliesGoal, PTL

-----------------------------------------------------------------------------

=============================================================================
