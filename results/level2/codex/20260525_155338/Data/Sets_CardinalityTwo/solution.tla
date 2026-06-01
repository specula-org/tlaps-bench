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

------------------------------------------------------------------

TwoMap(m, p) == [i \in 1..2 |-> IF i = 1 THEN m ELSE p]

LEMMA TwoMapBijection ==
  ASSUME NEW m, NEW p, m # p
  PROVE  IsBijection(TwoMap(m, p), 1..2, {m,p})
PROOF BY DEF IsBijection, TwoMap

LEMMA TwoElementSetFinite ==
  ASSUME NEW m, NEW p, m # p
  PROVE  IsFiniteSet({m,p})
PROOF
  <1>1. IsBijection(TwoMap(m, p), 1..2, {m,p})
    BY TwoMapBijection
  <1>2. 2 \in Nat
    BY SMT
  <1>3. \E f : IsBijection(f, 1..2, {m,p})
    BY <1>1
  <1>4. QED
    BY <1>2, <1>3 DEF IsFiniteSet

THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
PROOF
  <1> SUFFICES ASSUME NEW m, NEW p, m # p
                PROVE  /\ IsFiniteSet({m,p})
                       /\ Cardinality({m,p}) = 2
    BY Zenon
  <1>1. IsFiniteSet({m,p})
    BY TwoElementSetFinite
  <1>2. IsBijection(TwoMap(m, p), 1..2, {m,p})
    BY TwoMapBijection
  <1>3. 2 \in Nat
    BY SMT
  <1>4. \E f : IsBijection(f, 1..2, {m,p})
    BY <1>2
  <1>5. 2 = Cardinality({m,p})
    BY CardinalityAxiom, <1>1, <1>3, <1>4
  <1>. QED
    BY <1>1, <1>5

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
