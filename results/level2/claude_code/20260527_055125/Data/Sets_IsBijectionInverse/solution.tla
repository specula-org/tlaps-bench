-------------------------------- MODULE Sets_IsBijectionInverse --------------------------------
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

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T,
         IsBijection(f, S, T)
  PROVE  \E g : IsBijection(g, T, S)
<1> DEFINE g == [y \in T |-> CHOOSE x \in S : f[x] = y]
<1>a. f \in [S -> T] BY DEF IsBijection
<1>b. \A x1, x2 \in S : (x1 # x2) => (f[x1] # f[x2]) BY DEF IsBijection
<1>c. \A y \in T : \E x \in S : f[x] = y BY DEF IsBijection
<1>d. ASSUME NEW y \in T
      PROVE  g[y] \in S /\ f[g[y]] = y
  <2>1. \E x \in S : f[x] = y BY <1>c
  <2>2. g[y] = CHOOSE x \in S : f[x] = y BY DEF g
  <2>3. (CHOOSE x \in S : f[x] = y) \in S
        /\ f[CHOOSE x \in S : f[x] = y] = y
        BY <2>1
  <2> QED BY <2>2, <2>3
<1>e. g \in [T -> S]
  <2>1. \A y \in T : g[y] \in S BY <1>d
  <2> QED BY <2>1 DEF g
<1>f1. \A y1, y2 \in T : (g[y1] = g[y2]) => (y1 = y2)
  <2>1. SUFFICES ASSUME NEW y1 \in T, NEW y2 \in T, g[y1] = g[y2]
                 PROVE  y1 = y2
        OBVIOUS
  <2>2. f[g[y1]] = y1 /\ f[g[y2]] = y2 BY <1>d
  <2>3. f[g[y1]] = f[g[y2]] BY <2>1
  <2> QED BY <2>2, <2>3
<1>f. \A y1, y2 \in T : (y1 # y2) => (g[y1] # g[y2])
  BY <1>f1
<1>g. ASSUME NEW x \in S
      PROVE  \E y \in T : g[y] = x
  <2>1. f[x] \in T BY <1>a
  <2>2. g[f[x]] \in S /\ f[g[f[x]]] = f[x] BY <2>1, <1>d
  <2>3. g[f[x]] = x
    <3>1. ASSUME g[f[x]] # x PROVE FALSE
      <4>1. f[g[f[x]]] # f[x] BY <2>2, <1>b, <3>1, x \in S
      <4> QED BY <4>1, <2>2
    <3> QED BY <3>1
  <2> QED BY <2>3, <2>1
<1>h. IsBijection(g, T, S) BY <1>e, <1>f, <1>g DEF IsBijection
<1> QED BY <1>h

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
