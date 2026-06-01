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

InverseMap(f, S, T) == [t \in T |-> CHOOSE s \in S : f[s] = t]

LEMMA InverseMapValues ==
  ASSUME NEW f, NEW S, NEW T,
         IsBijection(f, S, T)
  PROVE  \A t \in T :
           /\ InverseMap(f, S, T)[t] \in S
           /\ f[InverseMap(f, S, T)[t]] = t
PROOF
<1>1. \A t \in T : \E s \in S : f[s] = t
  BY DEF IsBijection
<1>2. \A t \in T :
          /\ (CHOOSE s \in S : f[s] = t) \in S
          /\ f[(CHOOSE s \in S : f[s] = t)] = t
  BY <1>1
<1>. QED BY <1>2 DEF InverseMap

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
PROOF
<1> DEFINE g == InverseMap(f, S, T)
<1>1. /\ f \in [S -> T]
       /\ \A x, y \in S : (x # y) => (f[x] # f[y])
       /\ \A y \in T : \E x \in S : f[x] = y
  BY DEF IsBijection
<1>2. \A t \in T :
         /\ g[t] \in S
         /\ f[g[t]] = t
  BY InverseMapValues DEF g
<1>3. g \in [T -> S]
  BY <1>2 DEF g, InverseMap
<1>4. \A u, v \in T : (u # v) => (g[u] # g[v])
PROOF
  <2> SUFFICES ASSUME NEW u \in T, NEW v \in T, u # v
                 PROVE  g[u] # g[v]
    BY Zenon
  <2>1. /\ f[g[u]] = u
         /\ f[g[v]] = v
    BY <1>2
  <2>. QED BY <2>1
<1>5. \A s \in S : \E t \in T : g[t] = s
PROOF
  <2> SUFFICES ASSUME NEW s \in S
                 PROVE  \E t \in T : g[t] = s
    BY Zenon
  <2>1. f[s] \in T
    BY <1>1
  <2>2. /\ g[f[s]] \in S
         /\ f[g[f[s]]] = f[s]
    BY <1>2, <2>1
  <2>3. g[f[s]] = s
    BY <1>1, <2>2
  <2>. QED BY <2>1, <2>3
<1>6. IsBijection(g, T, S)
  BY <1>3, <1>4, <1>5 DEF IsBijection
<1>. QED BY <1>6

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
