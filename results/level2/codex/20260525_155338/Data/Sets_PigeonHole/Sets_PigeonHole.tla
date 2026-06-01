-------------------------------- MODULE Sets_PigeonHole --------------------------------
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

FT == INSTANCE FunctionTheorems

LEMMA IsBijectionImpliesFTBijection ==
  ASSUME NEW f, NEW S, NEW T,
         IsBijection(f, S, T)
  PROVE  f \in FT!Bijection(S, T)
  BY DEF IsBijection, FT!Bijection, FT!Injection, FT!Surjection,
         FT!IsInjective

LEMMA NoCollisionImpliesFTInjection ==
  ASSUME NEW f, NEW S, NEW T,
         f \in [S -> T],
         \A x, y \in S : x # y => f[x] # f[y]
  PROVE  f \in FT!Injection(S, T)
  BY DEF FT!Injection, FT!IsInjective

LEMMA CardinalityWitness ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  /\ Cardinality(S) \in Nat
         /\ \E f : IsBijection(f, 1..Cardinality(S), S)
<1>1. (Cardinality(S) = Cardinality(S)) <=>
        (Cardinality(S) \in Nat
          /\ \E f : IsBijection(f, 1..Cardinality(S), S))
  BY CardinalityAxiom
<1>2. Cardinality(S) = Cardinality(S)
  OBVIOUS
<1> QED
  BY <1>1, <1>2

LEMMA InjectionGivesNatInjection ==
  ASSUME NEW S, NEW T,
         NEW n \in Nat, NEW m \in Nat,
         NEW bS, IsBijection(bS, 1..n, S),
         NEW bT, IsBijection(bT, 1..m, T),
         NEW f \in FT!Injection(S, T)
  PROVE  FT!ExistsInjection(1..n, 1..m)
<1>1. bS \in FT!Bijection(1..n, S)
  BY IsBijectionImpliesFTBijection
<1>2. bS \in FT!Injection(1..n, S)
  BY <1>1, FT!Fun_BijectionProperties
<1>3. bT \in FT!Bijection(1..m, T)
  BY IsBijectionImpliesFTBijection
<1>4. FT!Inverse(bT, 1..m, T) \in FT!Bijection(T, 1..m)
  BY <1>3, FT!Fun_BijInverse
<1>5. FT!Inverse(bT, 1..m, T) \in FT!Injection(T, 1..m)
  BY <1>4, FT!Fun_BijectionProperties
<1>6. [x \in 1..n |-> f[bS[x]]] \in FT!Injection(1..n, T)
  BY <1>2, FT!Fun_InjTransitive
<1>7. [x \in 1..n |->
          FT!Inverse(bT, 1..m, T)[[y \in 1..n |-> f[bS[y]]][x]]]
         \in FT!Injection(1..n, 1..m)
  BY <1>5, <1>6, FT!Fun_InjTransitive
<1> QED
  BY <1>7 DEF FT!ExistsInjection

LEMMA InjectionCardinalityLeq ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW T, IsFiniteSet(T),
         NEW f \in FT!Injection(S, T)
  PROVE  Cardinality(S) <= Cardinality(T)
<1>1. /\ Cardinality(S) \in Nat
      /\ \E bS : IsBijection(bS, 1..Cardinality(S), S)
  BY CardinalityWitness
<1>2. /\ Cardinality(T) \in Nat
      /\ \E bT : IsBijection(bT, 1..Cardinality(T), T)
  BY CardinalityWitness
<1>3. PICK bS : IsBijection(bS, 1..Cardinality(S), S)
  BY <1>1
<1>4. PICK bT : IsBijection(bT, 1..Cardinality(T), T)
  BY <1>2
<1>5. FT!ExistsInjection(1..Cardinality(S), 1..Cardinality(T))
  BY <1>1, <1>2, <1>3, <1>4, InjectionGivesNatInjection
<1> QED
  BY <1>1, <1>2, <1>5, FT!Fun_NatInjLeq

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
PROOF
<1>. SUFFICES ASSUME NEW S, NEW T,
                      IsFiniteSet(S),
                      IsFiniteSet(T),
                      Cardinality(T) < Cardinality(S)
              PROVE  \A f \in [S -> T] :
                       \E x, y \in S : x # y /\ f[x] = f[y]
  OBVIOUS
<1>1. ASSUME NEW f \in [S -> T]
       PROVE  \E x, y \in S : x # y /\ f[x] = f[y]
  <2>. SUFFICES ASSUME \A x, y \in S : x # y => f[x] # f[y]
                PROVE  FALSE
    BY Zenon
  <2>1. f \in FT!Injection(S, T)
    BY NoCollisionImpliesFTInjection
  <2>2. Cardinality(S) <= Cardinality(T)
    BY <2>1, InjectionCardinalityLeq
  <2>3. /\ Cardinality(S) \in Nat
        /\ Cardinality(T) \in Nat
    BY CardinalityWitness
  <2> QED
    BY <2>2, <2>3
<1> QED
  BY <1>1
-------------------------------------------------------

=============================================================================
