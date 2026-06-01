---- MODULE Consensus_CardinalitySetMinus ----
EXTENDS Integers, NaturalsInduction, TLAPS
(* ---- Content from module Sets ---- *)
  \** NB: Module NaturalsInduction comes from the TLAPS library, usually
  \** installed in /usr/local/lib/tlaps. Make sure this is in your Toolbox
  \** search path, see Preferences/TLA+ Preferences.

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y


IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

(****************************************************************************)
(* Finite sets and cardinality are defined in the TLA+ standard module      *)
(* FiniteSets, but this is not yet natively supported by TLAPS. For the     *)
(* time being, we use the following axiom for defining set cardinality.     *)
(****************************************************************************)
\* Cardinality(S) == CHOOSE n : (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

THEOREM CardinalityInNat == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
  PROOF OMITTED

THEOREM CardinalityPlusOne ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW x, x \notin S
    PROVE  /\ IsFiniteSet(S \cup {x})
           /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOne == \A m : /\ IsFiniteSet({m})
                                 /\ Cardinality({m}) = 1
  PROOF OMITTED

THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
  PROOF OMITTED

THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
  PROOF OMITTED

-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
  PROOF OMITTED

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
  PROOF OMITTED

THEOREM IsBijectionCardinality ==
  \A f, S, T : /\ IsFiniteSet(S)
               /\ IsFiniteSet(T)
               => (IsBijection(f, S, T) <=> Cardinality(S) = Cardinality(T))

LEMMA CardinalitySetMinus ==
      ASSUME NEW S, IsFiniteSet(S),
             NEW x \in S
      PROVE /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1
PROOF
  <1>1. PICK n \in Nat, f : IsBijection(f, 1..n, S)
    BY DEF IsFiniteSet
  <1>2. PICK k \in 1..n : f[k] = x
    BY <1>1 DEF IsBijection
  <1>3. n # 0
    BY <1>2
  <1>4. n - 1 \in Nat
    BY <1>1, <1>3
  <1>5. DEFINE r(i) == IF i < k THEN i ELSE i+1
                g == [i \in 1..(n-1) |-> f[r(i)]]
  <1>6. IsBijection(g, 1..(n-1), S \ {x})
    <2>1. g \in [1..(n-1) -> S \ {x}]
      <3>1. ASSUME NEW i \in 1..(n-1)
             PROVE  g[i] \in S \ {x}
        BY <1>1, <1>2 DEF IsBijection, g, r
      <3>. QED BY <3>1
    <2>2. \A i, j \in 1..(n-1) : (i # j) => (g[i] # g[j])
      <3>1. ASSUME NEW i \in 1..(n-1), NEW j \in 1..(n-1)
             PROVE  (i # j) => (g[i] # g[j])
        <4>1. ASSUME i # j
               PROVE  g[i] # g[j]
          <5>1. /\ r(i) \in 1..n
                 /\ r(j) \in 1..n
                 /\ r(i) # r(j)
            BY <1>2, <4>1 DEF r
          <5>2. /\ g[i] = f[r(i)]
                 /\ g[j] = f[r(j)]
            BY DEF g
          <5>. QED BY <1>1, <5>1, <5>2 DEF IsBijection
        <4>. QED BY <4>1
      <3>. QED BY <3>1
    <2>3. \A y \in S \ {x} : \E i \in 1..(n-1) : g[i] = y
      <3>1. ASSUME NEW y \in S \ {x}
             PROVE  \E i \in 1..(n-1) : g[i] = y
        <4>1. PICK p \in 1..n : f[p] = y
          BY <1>1, <3>1 DEF IsBijection, g, r
        <4>2. p # k
          BY <1>2, <3>1, <4>1
        <4>3. IF p < k THEN p \in 1..(n-1) /\ g[p] = y
                         ELSE p-1 \in 1..(n-1) /\ g[p-1] = y
          BY <1>2, <3>1, <4>1, <4>2
        <4>. QED BY <4>3
      <3>. QED BY <3>1
    <2>. QED BY <2>1, <2>2, <2>3 DEF IsBijection, g, r
  <1>7. IsFiniteSet(S \ {x})
    BY <1>4, <1>6 DEF IsFiniteSet
  <1>8. Cardinality(S \ {x}) = n - 1
    BY <1>4, <1>6, <1>7, CardinalityAxiom
  <1>9. Cardinality(S) = n
    BY <1>1, CardinalityAxiom
  <1>. QED BY <1>7, <1>8, <1>9

========================================
