-------------------------------- MODULE Sets_IsBijectionTransitive --------------------------------
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

-----------------------------------------------------------------------------

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U,
           IsBijection(f1, S, U),
           IsBijection(f2, U, T)
  PROVE  \E g : IsBijection(g, S, T)
PROOF
  <1> DEFINE g == [x \in S |-> f2[f1[x]]]
  <1>a. f1 \in [S -> U]
    BY DEF IsBijection
  <1>b. f2 \in [U -> T]
    BY DEF IsBijection
  <1>1. g \in [S -> T]
    <2> SUFFICES ASSUME NEW x \in S
                 PROVE  f2[f1[x]] \in T
      BY DEF g
    <2>1. f1[x] \in U
      BY <1>a
    <2> QED
      BY <2>1, <1>b
  <1>2. \A x, y \in S : (x # y) => (g[x] # g[y])
    <2> SUFFICES ASSUME NEW x \in S, NEW y \in S, x # y
                 PROVE  g[x] # g[y]
      OBVIOUS
    <2>1. f1[x] \in U /\ f1[y] \in U
      BY <1>a
    <2>2. f1[x] # f1[y]
      BY DEF IsBijection
    <2>3. f2[f1[x]] # f2[f1[y]]
      BY <2>1, <2>2 DEF IsBijection
    <2>4. g[x] = f2[f1[x]] /\ g[y] = f2[f1[y]]
      BY DEF g
    <2> QED
      BY <2>3, <2>4
  <1>3. \A y \in T : \E x \in S : g[x] = y
    <2> SUFFICES ASSUME NEW y \in T
                 PROVE  \E x \in S : g[x] = y
      OBVIOUS
    <2>1. PICK u \in U : f2[u] = y
      BY DEF IsBijection
    <2>2. PICK x \in S : f1[x] = u
      BY <2>1 DEF IsBijection
    <2>3. g[x] = f2[f1[x]]
      BY DEF g
    <2>4. g[x] = y
      BY <2>1, <2>2, <2>3
    <2> QED
      BY <2>4
  <1>4. IsBijection(g, S, T)
    BY <1>1, <1>2, <1>3 DEF IsBijection
  <1> QED
    BY <1>4

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
