-------------------------------- MODULE Sets_CardinalityOneConverse --------------------------------
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

------------------------------------------------------------------

LEMMA OneOneIsSingleton == 1..1 = {1}
  OBVIOUS

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
<1>1. \E f : IsBijection(f, 1..1, S)
  <2>1. 1 \in Nat
    OBVIOUS
  <2>2. (1 = Cardinality(S)) <=> ((1 \in Nat) /\ \E f : IsBijection(f, 1..1, S))
    BY CardinalityAxiom
  <2>3. 1 = Cardinality(S)
    OBVIOUS
  <2>. QED
    BY <2>1, <2>2, <2>3
<1>2. PICK f : IsBijection(f, 1..1, S)
  BY <1>1
<1>3. /\ f \in [1..1 -> S]
      /\ \A y \in S : \E x \in 1..1 : f[x] = y
  BY <1>2 DEF IsBijection
<1>4. 1 \in 1..1
  OBVIOUS
<1>5. f[1] \in S
  BY <1>3, <1>4
<1>6. \A y \in S : y = f[1]
  <2>1. TAKE y \in S
  <2>2. \E x \in 1..1 : f[x] = y
    BY <1>3
  <2>3. PICK x \in 1..1 : f[x] = y
    BY <2>2
  <2>4. x = 1
    BY <2>3
  <2>5. f[1] = y
    BY <2>3, <2>4
  <2>. QED
    BY <2>5
<1>7. S = {f[1]}
  BY <1>5, <1>6
<1>8. QED
  BY <1>7

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
