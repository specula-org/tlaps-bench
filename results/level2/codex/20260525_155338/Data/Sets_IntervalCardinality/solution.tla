-------------------------------- MODULE Sets_IntervalCardinality --------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y

IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

LEMMA EmptyIntervalBijection ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a > b
  PROVE  IsBijection([i \in 1..0 |-> i], 1..0, a..b)
PROOF
  BY SMT DEF IsBijection

LEMMA NonEmptyIntervalBijection ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b
  PROVE  LET n == b-a+1
             f == [i \in 1..n |-> a+i-1]
         IN  IsBijection(f, 1..n, a..b)
PROOF
  <1> DEFINE n == b-a+1
              f == [i \in 1..n |-> a+i-1]
  <1>1. f \in [1..n -> a..b]
    BY SMT DEF n, f
  <1>2. \A x, y \in 1..n : (x # y) => (f[x] # f[y])
    <2>. SUFFICES ASSUME NEW x \in 1..n, NEW y \in 1..n, x # y
                   PROVE  f[x] # f[y]
      BY SMT
    <2>1. f[x] = a+x-1
      BY SMT DEF f
    <2>2. f[y] = a+y-1
      BY SMT DEF f
    <2>3. a+x-1 # a+y-1
      BY SMT
    <2>. QED
      BY <2>1, <2>2, <2>3
  <1>3. \A y \in a..b : \E x \in 1..n : f[x] = y
    <2>. SUFFICES ASSUME NEW y \in a..b
                   PROVE  \E x \in 1..n : f[x] = y
      BY SMT
    <2>1. y-a+1 \in 1..n
      BY SMT DEF n
    <2>2. f[y-a+1] = y
      BY <2>1, SMT DEF f
    <2>. QED
      BY <2>1, <2>2
  <1>. QED
    BY <1>1, <1>2, <1>3 DEF IsBijection

THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
PROOF
  <1>1. CASE a > b
    <2>1. IsBijection([i \in 1..0 |-> i], 1..0, a..b)
      BY <1>1, EmptyIntervalBijection
    <2>2. IsFiniteSet(a..b)
      BY <2>1 DEF IsFiniteSet
    <2>3. 0 = Cardinality(a..b)
      BY <1>1, <2>1, <2>2, CardinalityAxiom DEF CardinalityAxiom
    <2>. QED
      BY <1>1, <2>2, <2>3
  <1>2. CASE a <= b
    <2> DEFINE n == b-a+1
                f == [i \in 1..n |-> a+i-1]
    <2>1. n \in Nat
      BY <1>2, SMT DEF n
    <2>2. IsBijection(f, 1..n, a..b)
      BY <1>2, NonEmptyIntervalBijection DEF n, f
    <2>3. IsFiniteSet(a..b)
      BY <2>1, <2>2 DEF IsFiniteSet
    <2>4. n = Cardinality(a..b)
      BY <2>1, <2>2, <2>3, CardinalityAxiom DEF CardinalityAxiom
    <2>. QED
      BY <1>2, <2>3, <2>4 DEF n
  <1>. QED
    BY <1>1, <1>2

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
