---- MODULE Consensus_IntervalCardinality ----
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
<1>1. DEFINE P(n) == \A c \in Nat : /\ IsFiniteSet(c..n)
                                  /\ Cardinality(c..n) = IF c > n THEN 0 ELSE n-c+1
<1>2. P(0)
  <2>1. SUFFICES ASSUME NEW c \in Nat
                  PROVE  /\ IsFiniteSet(c..0)
                         /\ Cardinality(c..0) = IF c > 0 THEN 0 ELSE 0-c+1
    BY DEF P
  <2>2. CASE c > 0
    <3>1. c..0 = {}
      BY <2>2, SMT
    <3>2. QED
      BY <3>1, CardinalityZero, <2>2
  <2>3. CASE c <= 0
    <3>1. c = 0
      BY <2>1, <2>3, Isa
    <3>2. c..0 = {0}
      BY <3>1, SMT
    <3>3. QED
      BY <3>1, <3>2, CardinalityOne
  <2>4. QED
    BY <2>2, <2>3
<1>3. \A n \in Nat : P(n) => P(n+1)
  <2>1. SUFFICES ASSUME NEW n \in Nat, P(n), NEW c \in Nat
                  PROVE  /\ IsFiniteSet(c..(n+1))
                         /\ Cardinality(c..(n+1)) = IF c > n+1 THEN 0 ELSE (n+1)-c+1
    BY DEF P
  <2>2. CASE c > n+1
    <3>1. c..(n+1) = {}
      BY <2>2, SMT
    <3>2. QED
      BY <3>1, CardinalityZero, <2>2
  <2>3. CASE c <= n+1
    <3>1. c..(n+1) = (c..n) \cup {n+1}
      BY <2>3, SMT
    <3>2. n+1 \notin c..n
      BY SMT
    <3>3. IsFiniteSet(c..n)
      BY <2>1 DEF P
    <3>4. Cardinality(c..n) = IF c > n THEN 0 ELSE n-c+1
      BY <2>1 DEF P
    <3>5. /\ IsFiniteSet((c..n) \cup {n+1})
           /\ Cardinality((c..n) \cup {n+1}) = Cardinality(c..n) + 1
      BY <3>2, <3>3, CardinalityPlusOne
    <3>6. IsFiniteSet(c..(n+1))
      BY <3>1, <3>5
    <3>7. Cardinality(c..n) + 1 = (n+1)-c+1
      <4>1. CASE c > n
        <5>1. c = n+1
          BY <2>3, <4>1, SMT
        <5>2. Cardinality(c..n) = 0
          BY <3>4, <4>1
        <5>3. QED
          BY <5>1, <5>2, Isa
      <4>2. CASE c <= n
        <5>1. Cardinality(c..n) = n-c+1
          BY <3>4, <4>2
        <5>2. QED
          BY <5>1, SMT
      <4>3. QED
        BY <4>1, <4>2
    <3>8. Cardinality(c..(n+1)) = (n+1)-c+1
      BY <3>1, <3>5, <3>7
    <3>9. QED
      BY <2>3, <3>6, <3>8
  <2>4. QED
    BY <2>2, <2>3
<1>4. \A n \in Nat : P(n)
  BY <1>2, <1>3, NatInduction
<1>5. QED
  BY <1>4 DEF P

========================================