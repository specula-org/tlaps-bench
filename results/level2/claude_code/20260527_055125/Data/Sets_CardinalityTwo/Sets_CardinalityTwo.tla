-------------------------------- MODULE Sets_CardinalityTwo --------------------------------
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

LEMMA TwoBijection ==
  ASSUME NEW m, NEW p, m # p
  PROVE  \E f : IsBijection(f, 1..2, {m, p})
PROOF
  <1> DEFINE f == [i \in 1..2 |-> IF i = 1 THEN m ELSE p]
  <1>1. 1 \in 1..2 /\ 2 \in 1..2 /\ 1 # 2
    BY SMT
  <1>2. f[1] = m
    BY <1>1
  <1>3. f[2] = p
    BY <1>1
  <1>4. \A i \in 1..2 : f[i] \in {m, p}
    <2> SUFFICES ASSUME NEW i \in 1..2
                PROVE  f[i] \in {m, p}
      OBVIOUS
    <2>1. i = 1 \/ i = 2
      BY SMT
    <2>2. CASE i = 1
      BY <2>2, <1>2
    <2>3. CASE i = 2
      BY <2>3, <1>3
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>5. f \in [1..2 -> {m, p}]
    BY <1>4
  <1>6. \A x, y \in 1..2 : (x # y) => (f[x] # f[y])
    <2> SUFFICES ASSUME NEW x \in 1..2, NEW y \in 1..2, x # y
                PROVE  f[x] # f[y]
      OBVIOUS
    <2>1. (x = 1 \/ x = 2) /\ (y = 1 \/ y = 2)
      BY SMT
    <2>2. CASE x = 1 /\ y = 2
      BY <2>2, <1>2, <1>3, m # p
    <2>3. CASE x = 2 /\ y = 1
      BY <2>3, <1>2, <1>3, m # p
    <2>4. QED BY <2>1, <2>2, <2>3, x # y
  <1>7. \A y \in {m, p} : \E x \in 1..2 : f[x] = y
    <2> SUFFICES ASSUME NEW y \in {m, p}
                PROVE  \E x \in 1..2 : f[x] = y
      OBVIOUS
    <2>1. y = m \/ y = p
      OBVIOUS
    <2>2. CASE y = m
      BY <1>1, <1>2, <2>2
    <2>3. CASE y = p
      BY <1>1, <1>3, <2>3
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>8. IsBijection(f, 1..2, {m, p})
    BY <1>5, <1>6, <1>7 DEF IsBijection
  <1>9. QED BY <1>8

------------------------------------------------------------------

THEOREM CardinalityTwo == \A m, p : m # p =>
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
PROOF
  <1> SUFFICES ASSUME NEW m, NEW p, m # p
              PROVE  /\ IsFiniteSet({m,p})
                     /\ Cardinality({m,p}) = 2
    OBVIOUS
  <1>1. 2 \in Nat
    BY SMT
  <1>2. \E f : IsBijection(f, 1..2, {m, p})
    BY TwoBijection
  <1>3. IsFiniteSet({m, p})
    <2>1. \E n \in Nat : \E f : IsBijection(f, 1..n, {m, p})
      BY <1>1, <1>2
    <2>2. QED BY <2>1 DEF IsFiniteSet
  <1>4. Cardinality({m, p}) = 2
    <2>1. \A n : (n = Cardinality({m, p})) <=>
              (n \in Nat) /\ \E f : IsBijection(f, 1..n, {m, p})
      BY <1>3, CardinalityAxiom
    <2>2. 2 = Cardinality({m, p})
      BY <1>1, <1>2, <2>1
    <2>3. QED BY <2>2
  <1>5. QED BY <1>3, <1>4

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
