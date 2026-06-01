---- MODULE GraphTheorem_CardinalitySetMinus ----
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
  <1>0. PICK n \in Nat, f : IsBijection(f, 1..n, S)
    BY DEF IsFiniteSet
  <1>1. n = Cardinality(S)
    BY <1>0, CardinalityAxiom DEF IsFiniteSet
  <1>2. PICK k \in 1..n : f[k] = x
    BY <1>0, x \in S DEF IsBijection
  <1>3. DEFINE T == S \ {x}
               g == [i \in 1..(n-1) |-> IF i < k THEN f[i] ELSE f[i+1]]
  <1>4. IsBijection(g, 1..(n-1), T)
      <2>1. g \in [1..(n-1) -> T]
          <3>1. ASSUME NEW i \in 1..(n-1)
                PROVE g[i] \in T
              <4>1. i \in 1..n /\ i+1 \in 1..n
                BY <3>1, k \in 1..n, SMT
              <4>2. CASE i < k
                <5>1. g[i] = f[i]
                  BY <4>2 DEF g
                <5>2. f[i] \in S
                  BY <1>0, <4>1 DEF IsBijection
                <5>3. f[i] # x
                  BY <1>0, <4>1, <4>2, f[k] = x DEF IsBijection
                <5>4. QED BY <5>1, <5>2, <5>3 DEF T
              <4>3. CASE ~(i < k)
                <5>1. g[i] = f[i+1]
                  BY <4>3 DEF g
                <5>2. i+1 \in 1..n
                  BY <4>1
                <5>3. f[i+1] \in S
                  BY <1>0, <5>2 DEF IsBijection
                <5>4. i+1 # k
                  BY <3>1, <4>3, k \in 1..n, SMT
                <5>5. f[i+1] # x
                  BY <1>0, <5>2, <5>4, f[k] = x DEF IsBijection
                <5>6. QED BY <5>1, <5>3, <5>5 DEF T
              <4>4. QED BY <4>2, <4>3
          <3>2. QED BY <3>1 DEF g
      <2>2. \A i, j \in 1..(n-1) : (i # j) => (g[i] # g[j])
          <3>1. ASSUME NEW i \in 1..(n-1), NEW j \in 1..(n-1), i # j
                PROVE g[i] # g[j]
              <4>1. LET h(a) == IF a < k THEN a ELSE a+1
                    IN /\ h(i) \in 1..n
                       /\ h(j) \in 1..n
                       /\ h(i) # h(j)
                       /\ g[i] = f[h(i)]
                       /\ g[j] = f[h(j)]
                BY <3>1, k \in 1..n DEF g, Nat
              <4>2. QED BY <1>0, <4>1 DEF IsBijection
          <3>2. QED BY <3>1
      <2>3. \A y \in T : \E i \in 1..(n-1) : g[i] = y
          <3>1. ASSUME NEW y \in T
                PROVE \E i \in 1..(n-1) : g[i] = y
              <4>1. y \in S /\ y # x
                BY <3>1 DEF T
              <4>2. PICK j \in 1..n : f[j] = y
                BY <1>0, <4>1 DEF IsBijection
              <4>3. j # k
                BY <4>1, f[k] = x, f[j] = y
              <4>4. CASE j < k
                <5>1. j \in 1..(n-1) /\ g[j] = f[j]
                  BY <4>4, j \in 1..n, k \in 1..n DEF g, Nat
                <5>2. QED BY <5>1, f[j] = y
              <4>5. CASE ~(j < k)
                <5>1. j > k
                  BY <4>3, <4>5, j \in 1..n, k \in 1..n DEF Nat
                <5>2. j-1 \in 1..(n-1) /\ g[j-1] = f[j]
                  BY <5>1, j \in 1..n, k \in 1..n DEF g, Nat
                <5>3. QED BY <5>2, f[j] = y
              <4>6. QED BY <4>4, <4>5
          <3>2. QED BY <3>1
      <2>4. QED BY <2>1, <2>2, <2>3 DEF IsBijection
  <1>5. IsFiniteSet(T)
    BY <1>4 DEF IsFiniteSet
  <1>6. Cardinality(T) = n-1
    BY <1>4, <1>5, CardinalityAxiom DEF IsFiniteSet
  <1>7. QED BY <1>1, <1>5, <1>6 DEF T

========================================
