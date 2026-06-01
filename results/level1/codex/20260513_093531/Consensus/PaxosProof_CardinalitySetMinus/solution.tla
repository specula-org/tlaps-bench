---- MODULE PaxosProof_CardinalitySetMinus ----
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
  <1>2. Cardinality(S) = n
    BY <1>1, CardinalityAxiom
  <1>3. PICK i \in 1..n : f[i] = x
    BY <1>1 DEF IsBijection
  <1>4. DEFINE g == [j \in 1..(n-1) |-> IF j < i THEN f[j] ELSE f[j+1]]
  <1>5. IsBijection(g, 1..(n-1), S \ {x})
    PROOF
      <2>1. g \in [1..(n-1) -> S \ {x}]
        PROOF
          <3>1. SUFFICES ASSUME NEW j \in 1..(n-1)
                  PROVE g[j] \in S \ {x}
            BY DEF g
          <3>2. CASE j < i
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>3. CASE ~(j < i)
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>4. QED BY <3>2, <3>3
      <2>2. \A y, z \in 1..(n-1) : (y # z) => (g[y] # g[z])
        PROOF
          <3>1. SUFFICES ASSUME NEW y \in 1..(n-1), NEW z \in 1..(n-1), y # z
                  PROVE g[y] # g[z]
            OBVIOUS
          <3>2. CASE y < i /\ z < i
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>3. CASE y < i /\ ~(z < i)
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>4. CASE ~(y < i) /\ z < i
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>5. CASE ~(y < i) /\ ~(z < i)
            BY <1>1, <1>3, <3>1 DEF IsBijection, g
          <3>6. QED BY <3>2, <3>3, <3>4, <3>5
      <2>3. \A y \in S \ {x} : \E j \in 1..(n-1) : g[j] = y
        PROOF
          <3>1. SUFFICES ASSUME NEW y \in S \ {x}
                  PROVE \E j \in 1..(n-1) : g[j] = y
            OBVIOUS
          <3>2. PICK k \in 1..n : f[k] = y
            BY <1>1, <3>1 DEF IsBijection
          <3>3. k # i
            BY <1>3, <3>1, <3>2
          <3>4. CASE k < i
            BY <1>3, <3>2, <3>4 DEF g
          <3>5. CASE ~(k < i)
            BY <1>3, <3>2, <3>3, <3>5 DEF g
          <3>6. QED BY <3>4, <3>5
      <2>4. QED BY <2>1, <2>2, <2>3 DEF IsBijection
  <1>6. IsFiniteSet(S \ {x})
    BY <1>5 DEF IsFiniteSet
  <1>7. Cardinality(S \ {x}) = n - 1
    BY <1>5, <1>6, CardinalityAxiom
  <1>8. QED BY <1>2, <1>6, <1>7

========================================
