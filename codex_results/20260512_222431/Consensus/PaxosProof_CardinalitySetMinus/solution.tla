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
<1>1. x \notin S \ {x}  OBVIOUS
<1>2. S = (S \ {x}) \cup {x}  OBVIOUS
<1>3. IsFiniteSet(S \ {x})
  <2>1. PICK n \in Nat : \E f : IsBijection(f, 1..n, S)
    BY DEF IsFiniteSet
  <2>2. PICK f : IsBijection(f, 1..n, S)
    BY <2>1
  <2>3. PICK k \in 1..n : f[k] = x
    BY <2>2 DEF IsBijection
  <2>4. DEFINE g == [i \in 1..(n-1) |-> IF i < k THEN f[i] ELSE f[i+1]]
  <2>4a. DEFINE h(i) == IF i < k THEN i ELSE i + 1
  <2>5. g \in [1..(n-1) -> S \ {x}]
  PROOF
    <3>1. ASSUME NEW i \in 1..(n-1) PROVE g[i] \in S \ {x}
      BY <2>2, <2>3 DEF g, IsBijection
    <3>. QED BY <3>1 DEF g
  <2>6. \A i, j \in 1..(n-1) : (i # j) => (g[i] # g[j])
  PROOF
    <3>1. ASSUME NEW i \in 1..(n-1), NEW j \in 1..(n-1), i # j
          PROVE g[i] # g[j]
    PROOF
      <4>1. h(i) \in 1..n /\ h(j) \in 1..n /\ h(i) # h(j)
        BY <3>1 DEF h
      <4>2. g[i] = f[h(i)] /\ g[j] = f[h(j)]
        BY <3>1 DEF g, h
      <4>. QED BY <2>2, <4>1, <4>2 DEF IsBijection
    <3>. QED BY <3>1
  <2>7. \A y \in S \ {x} : \E i \in 1..(n-1) : g[i] = y
  PROOF
    <3>1. ASSUME NEW y \in S \ {x} PROVE \E i \in 1..(n-1) : g[i] = y
    PROOF
      <4>1. PICK i \in 1..n : f[i] = y
        BY <2>2, <3>1 DEF IsBijection
      <4>2. i # k
        BY <2>3, <3>1, <4>1
      <4>3. CASE i < k
        <5>1. i \in 1..(n-1) /\ g[i] = y
          BY <2>3, <3>1, <4>1, <4>3 DEF g
        <5>. QED BY <5>1
      <4>4. CASE i > k
        <5>1. i - 1 \in 1..(n-1) /\ g[i-1] = y
          BY <2>3, <3>1, <4>1, <4>4 DEF g
        <5>. QED BY <5>1
      <4>. QED BY <4>2, <4>3, <4>4
    <3>. QED BY <3>1
  <2>8. IsBijection(g, 1..(n-1), S \ {x})
    BY <2>5, <2>6, <2>7 DEF IsBijection
  <2>9. n - 1 \in Nat
    BY <2>1, <2>3
  <2>. QED BY <2>8, <2>9 DEF IsFiniteSet
<1>4. /\ IsFiniteSet((S \ {x}) \cup {x})
       /\ Cardinality((S \ {x}) \cup {x}) = Cardinality(S \ {x}) + 1
  BY <1>1, <1>3, CardinalityPlusOne
<1>5. Cardinality(S) = Cardinality(S \ {x}) + 1
  BY <1>2, <1>4
<1>. QED BY <1>3, <1>5, CardinalityInNat

========================================
