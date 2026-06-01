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

LEMMA EmptyBijection ==
  ASSUME NEW T, T = {}
  PROVE  /\ 0 \in Nat
         /\ \E f : IsBijection(f, 1..0, T)
PROOF
  <1>1 0 \in Nat OBVIOUS
  <1>2 1..0 = {} OBVIOUS
  <1> DEFINE f0 == [x \in {} |-> x]
  <1>3 IsBijection(f0, 1..0, T)
    BY <1>2 DEF IsBijection
  <1>4 \E f : IsBijection(f, 1..0, T)
    BY <1>3
  <1> QED BY <1>1, <1>4

LEMMA IntervalBijectionExists ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a \leq b
  PROVE  /\ (b - a + 1) \in Nat
         /\ \E f : IsBijection(f, 1..(b-a+1), a..b)
PROOF
  <1>1 (b - a + 1) \in Nat
    OBVIOUS
  <1> DEFINE n == b - a + 1
  <1> DEFINE g == [i \in 1..n |-> a + i - 1]
  <1>2 ASSUME NEW i \in 1..n
       PROVE  a + i - 1 \in a..b
    BY <1>2
  <1>3 g \in [1..n -> a..b]
    BY <1>2
  <1>4 ASSUME NEW x \in 1..n, NEW y \in 1..n, x # y
       PROVE  g[x] # g[y]
    <2>1 g[x] = a + x - 1
      OBVIOUS
    <2>2 g[y] = a + y - 1
      OBVIOUS
    <2>3 a + x - 1 # a + y - 1
      BY <1>4
    <2> QED BY <2>1, <2>2, <2>3
  <1>5 ASSUME NEW y \in a..b
       PROVE  \E x \in 1..n : g[x] = y
    <2>1 a \leq y /\ y \leq b
      OBVIOUS
    <2>2 (y - a + 1) \in 1..n
      BY <2>1
    <2>3 g[y - a + 1] = a + (y - a + 1) - 1
      BY <2>2
    <2>4 a + (y - a + 1) - 1 = y
      BY <2>1
    <2>5 g[y - a + 1] = y
      BY <2>3, <2>4
    <2> QED BY <2>2, <2>5
  <1>6 IsBijection(g, 1..n, a..b)
    BY <1>3, <1>4, <1>5 DEF IsBijection
  <1>7 \E f : IsBijection(f, 1..n, a..b)
    BY <1>6
  <1> QED BY <1>1, <1>7

THEOREM IntervalCardinality ==
  ASSUME NEW a \in Nat, NEW b \in Nat
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
PROOF
  <1>1 CASE a > b
    <2>1 a..b = {}
      BY <1>1
    <2>2 0 \in Nat /\ \E f : IsBijection(f, 1..0, a..b)
      BY <2>1, EmptyBijection
    <2>3 IsFiniteSet(a..b)
      BY <2>2 DEF IsFiniteSet
    <2>4 (0 = Cardinality(a..b)) <=> ((0 \in Nat) /\ \E f : IsBijection(f, 1..0, a..b))
      BY <2>3, CardinalityAxiom
    <2>5 Cardinality(a..b) = 0
      BY <2>2, <2>4
    <2>6 (IF a > b THEN 0 ELSE b-a+1) = 0
      BY <1>1
    <2> QED BY <2>3, <2>5, <2>6
  <1>2 CASE ~(a > b)
    <2>0 a \leq b
      BY <1>2
    <2>1 (b - a + 1) \in Nat /\ \E f : IsBijection(f, 1..(b-a+1), a..b)
      BY <2>0, IntervalBijectionExists
    <2>2 IsFiniteSet(a..b)
      BY <2>1 DEF IsFiniteSet
    <2>3 ((b-a+1) = Cardinality(a..b)) <=>
         (((b-a+1) \in Nat) /\ \E f : IsBijection(f, 1..(b-a+1), a..b))
      BY <2>2, CardinalityAxiom
    <2>4 Cardinality(a..b) = b - a + 1
      BY <2>1, <2>3
    <2>5 (IF a > b THEN 0 ELSE b-a+1) = b - a + 1
      BY <1>2
    <2> QED BY <2>2, <2>4, <2>5
  <1> QED BY <1>1, <1>2

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
