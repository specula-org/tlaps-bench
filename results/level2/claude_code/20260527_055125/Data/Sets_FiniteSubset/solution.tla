-------------------------------- MODULE Sets_FiniteSubset --------------------------------
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

ExistsBij(n, S) == \E f : IsBijection(f, 1..n, S)

RestrictFn(f, n) == [i \in 1..n |-> f[i]]
ExtendFn(f, m, x) == [i \in 1..(m+1) |-> IF i = m+1 THEN x ELSE f[i]]

------------------------------------------------------------------

LEMMA EmptyInterval == 1..0 = {}
PROOF OBVIOUS

LEMMA EmptyBijection == IsBijection([x \in {} |-> x], 1..0, {})
PROOF
  <1> DEFINE f == [x \in {} |-> x]
  <1>1. 1..0 = {} BY EmptyInterval
  <1>2. f \in [{} -> {}] OBVIOUS
  <1>3. f \in [1..0 -> {}] BY <1>1, <1>2
  <1>4. \A xx, yy \in 1..0 : (xx # yy) => (f[xx] # f[yy])
    BY <1>1
  <1>5. \A y \in {} : \E xx \in 1..0 : f[xx] = y
    OBVIOUS
  <1>6. QED BY <1>3, <1>4, <1>5 DEF IsBijection

LEMMA EmptyFinite == IsFiniteSet({})
PROOF
  <1>1. \E f : IsBijection(f, 1..0, {}) BY EmptyBijection
  <1>2. 0 \in Nat OBVIOUS
  <1>3. \E n \in Nat : \E f : IsBijection(f, 1..n, {}) BY <1>1, <1>2
  <1>4. QED BY <1>3 DEF IsFiniteSet

LEMMA CardCharacterization ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  /\ Cardinality(S) \in Nat
         /\ ExistsBij(Cardinality(S), S)
PROOF
  <1>1. \A n : (n = Cardinality(S)) <=>
              (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
    BY CardinalityAxiom
  <1>2. (Cardinality(S) = Cardinality(S)) <=>
        (Cardinality(S) \in Nat) /\ \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>1
  <1>3. (Cardinality(S) \in Nat) /\ \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>2
  <1>4. QED BY <1>3 DEF ExistsBij

LEMMA BijImpliesCard ==
  ASSUME NEW S, NEW n \in Nat, ExistsBij(n, S)
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) = n
PROOF
  <1>1. IsFiniteSet(S) BY DEF IsFiniteSet, ExistsBij
  <1>2. \A m : (m = Cardinality(S)) <=>
              (m \in Nat) /\ \E f : IsBijection(f, 1..m, S)
    BY <1>1, CardinalityAxiom
  <1>3. (n = Cardinality(S)) <=>
        (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
    BY <1>2
  <1>4. (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
    BY DEF ExistsBij
  <1>5. n = Cardinality(S) BY <1>3, <1>4
  <1>6. QED BY <1>1, <1>5

LEMMA EmptyCard == Cardinality({}) = 0
PROOF
  <1>1. IsFiniteSet({}) BY EmptyFinite
  <1>2. ExistsBij(0, {}) BY EmptyBijection DEF ExistsBij
  <1>3. 0 \in Nat OBVIOUS
  <1>4. QED BY <1>2, <1>3, BijImpliesCard

LEMMA ZeroCardEmpty ==
  ASSUME NEW T, IsFiniteSet(T), Cardinality(T) = 0
  PROVE  T = {}
PROOF
  <1>1. ExistsBij(Cardinality(T), T) BY CardCharacterization
  <1>2. ExistsBij(0, T) BY <1>1
  <1>3. PICK f : IsBijection(f, 1..0, T) BY <1>2 DEF ExistsBij
  <1>4. \A y \in T : \E xx \in 1..0 : f[xx] = y BY <1>3 DEF IsBijection
  <1>5. 1..0 = {} BY EmptyInterval
  <1>6. QED BY <1>4, <1>5

------------------------------------------------------------------

LEMMA RestrictBij ==
  ASSUME NEW T, NEW n \in Nat, NEW f, NEW x,
         IsBijection(f, 1..(n+1), T),
         f[n+1] = x
  PROVE  IsBijection(RestrictFn(f, n), 1..n, T \ {x})
PROOF
  <1>1. f \in [1..(n+1) -> T] BY DEF IsBijection
  <1>2. \A i, j \in 1..(n+1) : (i # j) => (f[i] # f[j]) BY DEF IsBijection
  <1>3. \A y \in T : \E i \in 1..(n+1) : f[i] = y BY DEF IsBijection
  <1>4. n+1 \in 1..(n+1) OBVIOUS
  <1>5. x \in T BY <1>1, <1>4
  <1>6. \A i \in 1..n : RestrictFn(f, n)[i] = f[i] BY DEF RestrictFn
  <1>7. \A i \in 1..n : i \in 1..(n+1) OBVIOUS
  <1>8. \A i \in 1..n : i # n+1 OBVIOUS
  <1>9. \A i \in 1..n : f[i] # x
    <2> TAKE i \in 1..n
    <2>1. i \in 1..(n+1) BY <1>7
    <2>2. i # n+1 BY <1>8
    <2>3. f[i] # f[n+1] BY <2>1, <2>2, <1>2, <1>4
    <2>4. QED BY <2>3
  <1>10. \A i \in 1..n : RestrictFn(f, n)[i] \in T \ {x}
    <2> TAKE i \in 1..n
    <2>1. RestrictFn(f, n)[i] = f[i] BY <1>6
    <2>2. f[i] \in T BY <1>7, <1>1
    <2>3. f[i] # x BY <1>9
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>11. RestrictFn(f, n) \in [1..n -> T \ {x}]
    BY <1>10 DEF RestrictFn
  <1>12. \A i, j \in 1..n : (i # j) => (RestrictFn(f, n)[i] # RestrictFn(f, n)[j])
    <2> TAKE i, j \in 1..n
    <2> HAVE i # j
    <2>1. i \in 1..(n+1) /\ j \in 1..(n+1) BY <1>7
    <2>2. f[i] # f[j] BY <2>1, <1>2
    <2>3. RestrictFn(f, n)[i] = f[i] /\ RestrictFn(f, n)[j] = f[j] BY <1>6
    <2>4. QED BY <2>2, <2>3
  <1>13. \A y \in T \ {x} : \E i \in 1..n : RestrictFn(f, n)[i] = y
    <2> TAKE y \in T \ {x}
    <2>1. y \in T OBVIOUS
    <2>2. PICK i \in 1..(n+1) : f[i] = y BY <2>1, <1>3
    <2>3. y # x OBVIOUS
    <2>4. f[n+1] = x OBVIOUS
    <2>5. i # n+1 BY <2>2, <2>3, <2>4
    <2>6. i \in 1..n BY <2>2, <2>5
    <2>7. RestrictFn(f, n)[i] = f[i] BY <2>6, <1>6
    <2>8. RestrictFn(f, n)[i] = y BY <2>7, <2>2
    <2>9. QED BY <2>6, <2>8
  <1>14. QED BY <1>11, <1>12, <1>13 DEF IsBijection

LEMMA RemoveElementCard ==
  ASSUME NEW T, IsFiniteSet(T),
         NEW n \in Nat, Cardinality(T) = n+1
  PROVE  \E x \in T :
            /\ IsFiniteSet(T \ {x})
            /\ Cardinality(T \ {x}) = n
PROOF
  <1>1. ExistsBij(Cardinality(T), T) BY CardCharacterization
  <1>2. ExistsBij(n+1, T) BY <1>1
  <1>3. PICK f : IsBijection(f, 1..(n+1), T) BY <1>2 DEF ExistsBij
  <1>4. f \in [1..(n+1) -> T] BY <1>3 DEF IsBijection
  <1>5. n+1 \in 1..(n+1) OBVIOUS
  <1> DEFINE x == f[n+1]
  <1>6. x \in T BY <1>4, <1>5
  <1>7. IsBijection(RestrictFn(f, n), 1..n, T \ {x})
    BY <1>3, RestrictBij
  <1>8. ExistsBij(n, T \ {x}) BY <1>7 DEF ExistsBij
  <1>9. IsFiniteSet(T \ {x}) /\ Cardinality(T \ {x}) = n
    BY <1>8, BijImpliesCard
  <1>10. QED BY <1>6, <1>9

------------------------------------------------------------------

LEMMA ExtendBij ==
  ASSUME NEW S, NEW x, x \notin S,
         NEW m \in Nat, NEW f, IsBijection(f, 1..m, S)
  PROVE  IsBijection(ExtendFn(f, m, x), 1..(m+1), S \cup {x})
PROOF
  <1>1. f \in [1..m -> S] BY DEF IsBijection
  <1>2. \A i, j \in 1..m : (i # j) => (f[i] # f[j]) BY DEF IsBijection
  <1>3. \A y \in S : \E i \in 1..m : f[i] = y BY DEF IsBijection
  <1>4. m+1 \in 1..(m+1) OBVIOUS
  <1>5. ExtendFn(f, m, x)[m+1] = x BY DEF ExtendFn
  <1>6. \A i \in 1..m : ExtendFn(f, m, x)[i] = f[i]
    <2> TAKE i \in 1..m
    <2>1. i \in 1..(m+1) OBVIOUS
    <2>2. i # m+1 OBVIOUS
    <2>3. QED BY <2>1, <2>2 DEF ExtendFn
  <1>7. \A i \in 1..(m+1) : ExtendFn(f, m, x)[i] \in S \cup {x}
    <2> TAKE i \in 1..(m+1)
    <2>1. CASE i = m+1
      <3>1. ExtendFn(f, m, x)[i] = x BY <2>1 DEF ExtendFn
      <3>2. QED BY <3>1
    <2>2. CASE i # m+1
      <3>1. i \in 1..m BY <2>2
      <3>2. ExtendFn(f, m, x)[i] = f[i] BY <3>1, <1>6
      <3>3. f[i] \in S BY <3>1, <1>1
      <3>4. QED BY <3>2, <3>3
    <2>3. QED BY <2>1, <2>2
  <1>8. ExtendFn(f, m, x) \in [1..(m+1) -> S \cup {x}]
    BY <1>7 DEF ExtendFn
  <1>9. \A i, j \in 1..(m+1) :
           (i # j) => (ExtendFn(f, m, x)[i] # ExtendFn(f, m, x)[j])
    <2> TAKE i, j \in 1..(m+1)
    <2> HAVE i # j
    <2>1. CASE i = m+1 /\ j # m+1
      <3>1. ExtendFn(f, m, x)[i] = x BY <2>1 DEF ExtendFn
      <3>2. j \in 1..m BY <2>1
      <3>3. ExtendFn(f, m, x)[j] = f[j] BY <3>2, <1>6
      <3>4. f[j] \in S BY <3>2, <1>1
      <3>5. ExtendFn(f, m, x)[j] \in S BY <3>3, <3>4
      <3>6. ExtendFn(f, m, x)[j] # x BY <3>5
      <3>7. QED BY <3>1, <3>6
    <2>2. CASE j = m+1 /\ i # m+1
      <3>1. ExtendFn(f, m, x)[j] = x BY <2>2 DEF ExtendFn
      <3>2. i \in 1..m BY <2>2
      <3>3. ExtendFn(f, m, x)[i] = f[i] BY <3>2, <1>6
      <3>4. f[i] \in S BY <3>2, <1>1
      <3>5. ExtendFn(f, m, x)[i] \in S BY <3>3, <3>4
      <3>6. ExtendFn(f, m, x)[i] # x BY <3>5
      <3>7. QED BY <3>1, <3>6
    <2>3. CASE i # m+1 /\ j # m+1
      <3>1. i \in 1..m /\ j \in 1..m BY <2>3
      <3>2. ExtendFn(f, m, x)[i] = f[i] /\ ExtendFn(f, m, x)[j] = f[j]
        BY <3>1, <1>6
      <3>3. f[i] # f[j] BY <3>1, <1>2
      <3>4. QED BY <3>2, <3>3
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>10. \A y \in S \cup {x} : \E i \in 1..(m+1) : ExtendFn(f, m, x)[i] = y
    <2> TAKE y \in S \cup {x}
    <2>1. CASE y = x
      <3>1. ExtendFn(f, m, x)[m+1] = x BY <1>5
      <3>2. ExtendFn(f, m, x)[m+1] = y BY <3>1, <2>1
      <3>3. QED BY <1>4, <3>2
    <2>2. CASE y # x
      <3>1. y \in S BY <2>2
      <3>2. PICK i \in 1..m : f[i] = y BY <3>1, <1>3
      <3>3. ExtendFn(f, m, x)[i] = f[i] BY <3>2, <1>6
      <3>4. ExtendFn(f, m, x)[i] = y BY <3>3, <3>2
      <3>5. i \in 1..(m+1) BY <3>2
      <3>6. QED BY <3>4, <3>5
    <2>3. QED BY <2>1, <2>2
  <1>11. QED BY <1>8, <1>9, <1>10 DEF IsBijection

LEMMA AddElementCard ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW x, x \notin S,
         NEW m \in Nat, Cardinality(S) = m
  PROVE  /\ IsFiniteSet(S \cup {x})
         /\ Cardinality(S \cup {x}) = m+1
PROOF
  <1>1. ExistsBij(Cardinality(S), S) BY CardCharacterization
  <1>2. ExistsBij(m, S) BY <1>1
  <1>3. PICK f : IsBijection(f, 1..m, S) BY <1>2 DEF ExistsBij
  <1>4. IsBijection(ExtendFn(f, m, x), 1..(m+1), S \cup {x})
    BY <1>3, ExtendBij
  <1>5. ExistsBij(m+1, S \cup {x}) BY <1>4 DEF ExistsBij
  <1>6. m+1 \in Nat OBVIOUS
  <1>7. QED BY <1>5, <1>6, BijImpliesCard

------------------------------------------------------------------

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
PROOF
  <1> DEFINE P(n) == \A T2, S2 :
       (IsFiniteSet(T2) /\ Cardinality(T2) = n /\ S2 \subseteq T2) =>
       (IsFiniteSet(S2) /\ Cardinality(S2) \leq n)
  <1>1. P(0)
    <2> SUFFICES ASSUME NEW T2, NEW S2,
                       IsFiniteSet(T2), Cardinality(T2) = 0, S2 \subseteq T2
                PROVE  IsFiniteSet(S2) /\ Cardinality(S2) \leq 0
      BY DEF P
    <2>1. T2 = {} BY ZeroCardEmpty
    <2>2. S2 = {} BY <2>1
    <2>3. IsFiniteSet({}) BY EmptyFinite
    <2>4. Cardinality({}) = 0 BY EmptyCard
    <2>5. QED BY <2>2, <2>3, <2>4
  <1>2. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n+1)
    <2> SUFFICES ASSUME NEW T2, NEW S2,
                       IsFiniteSet(T2), Cardinality(T2) = n+1, S2 \subseteq T2
                PROVE  IsFiniteSet(S2) /\ Cardinality(S2) \leq n+1
      BY DEF P
    <2>1. PICK x \in T2 :
              IsFiniteSet(T2 \ {x}) /\ Cardinality(T2 \ {x}) = n
      BY RemoveElementCard
    <2>2. CASE x \in S2
      <3>1. S2 \ {x} \subseteq T2 \ {x}
        OBVIOUS
      <3>2. IsFiniteSet(T2 \ {x}) /\ Cardinality(T2 \ {x}) = n
        BY <2>1
      <3>3. IsFiniteSet(S2 \ {x}) /\ Cardinality(S2 \ {x}) \leq n
        BY <3>1, <3>2, P(n) DEF P
      <3>4. PICK m \in Nat : Cardinality(S2 \ {x}) = m /\ m \leq n
        BY <3>3, CardCharacterization
      <3>5. x \notin S2 \ {x} OBVIOUS
      <3>6. IsFiniteSet((S2 \ {x}) \cup {x}) /\
            Cardinality((S2 \ {x}) \cup {x}) = m+1
        BY <3>3, <3>4, <3>5, AddElementCard
      <3>7. (S2 \ {x}) \cup {x} = S2 BY <2>2
      <3>8. IsFiniteSet(S2) /\ Cardinality(S2) = m+1 BY <3>6, <3>7
      <3>9. m+1 \leq n+1 BY <3>4
      <3>10. QED BY <3>8, <3>9
    <2>3. CASE x \notin S2
      <3>1. S2 \subseteq T2 \ {x}
        BY <2>3
      <3>2. IsFiniteSet(T2 \ {x}) /\ Cardinality(T2 \ {x}) = n
        BY <2>1
      <3>3. IsFiniteSet(S2) /\ Cardinality(S2) \leq n
        BY <3>1, <3>2, P(n) DEF P
      <3>4. Cardinality(S2) \in Nat BY <3>3, CardCharacterization
      <3>5. Cardinality(S2) \leq n+1 BY <3>3, <3>4
      <3>6. QED BY <3>3, <3>5
    <2>4. QED BY <2>2, <2>3
  <1>3. HIDE DEF P
  <1>4. \A n \in Nat : P(n) BY <1>1, <1>2, NatInduction, Isa
  <1>5. Cardinality(TT) \in Nat BY CardCharacterization
  <1>6. P(Cardinality(TT)) BY <1>4, <1>5
  <1>7. IsFiniteSet(S) /\ Cardinality(S) \leq Cardinality(TT)
    BY <1>6 DEF P
  <1>8. QED BY <1>7
-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
