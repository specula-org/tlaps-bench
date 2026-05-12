-------------------------------- MODULE Sets_IntervalCardinality --------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS
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
PROOF
  <1> DEFINE P(n) == \A c \in Nat :
                       /\ IsFiniteSet(c..n)
                       /\ Cardinality(c..n) = IF c > n THEN 0 ELSE n-c+1
  <1>1. P(0)
    <2>1. SUFFICES ASSUME NEW c \in Nat
                   PROVE  /\ IsFiniteSet(c..0)
                          /\ Cardinality(c..0) = IF c > 0 THEN 0 ELSE 0-c+1
      BY DEF P
    <2>2. CASE c = 0
      <3>1. \A x : x \in c..0 <=> x \in {0}
        BY <2>2, SMT
      <3>2. c..0 = {0}
        BY <3>1, SetExtensionality
      <3>3. QED
        BY <2>1, <2>2, <3>2, CardinalityOne, SMT
    <2>3. CASE c > 0
      <3>1. \A x : x \in c..0 <=> x \in {}
        BY <2>1, <2>3, SMT
      <3>2. c..0 = {}
        BY <3>1, SetExtensionality
      <3>3. QED
        BY <2>1, <2>3, <3>2, CardinalityZero, SMT
    <2>4. c = 0 \/ c > 0
      BY <2>1, SMT
    <2>5. QED
      BY <2>2, <2>3, <2>4
  <1>2. \A n \in Nat : P(n) => P(n+1)
    <2>1. SUFFICES ASSUME NEW n \in Nat, P(n), NEW c \in Nat
                   PROVE  /\ IsFiniteSet(c..(n+1))
                          /\ Cardinality(c..(n+1)) = IF c > n+1 THEN 0 ELSE n+1-c+1
      BY DEF P
    <2>2. CASE c > n+1
      <3>1. \A x : x \in c..(n+1) <=> x \in {}
        BY <2>1, <2>2, SMT
      <3>2. c..(n+1) = {}
        BY <3>1, SetExtensionality
      <3>3. QED
        BY <2>1, <2>2, <3>2, CardinalityZero, SMT
    <2>3. CASE c = n+1
      <3>1. \A x : x \in c..(n+1) <=> x \in {c}
        BY <2>1, <2>3, SMT
      <3>2. c..(n+1) = {c}
        BY <3>1, SetExtensionality
      <3>3. n+1-c+1 = 1
        BY <2>3, SMT
      <3>4. IsFiniteSet(c..(n+1))
        BY <3>2, CardinalityOne
      <3>5. Cardinality(c..(n+1)) = 1
        BY <3>2, CardinalityOne
      <3>6. QED
        BY <2>3, <3>3, <3>4, <3>5, SMT
    <2>4. CASE c < n+1
      <3>1. c \leq n
        BY <2>1, <2>4, Isa
      <3>2. \A x : x \in c..(n+1) <=> x \in (c..n) \cup {n+1}
        BY <2>1, <3>1, SMT
      <3>3. c..(n+1) = (c..n) \cup {n+1}
        BY <3>2, SetExtensionality
      <3>4. n+1 \notin c..n
        BY <2>1, SMT
      <3>5. /\ IsFiniteSet((c..n) \cup {n+1})
             /\ Cardinality((c..n) \cup {n+1}) = Cardinality(c..n) + 1
        BY <2>1, <3>4, CardinalityPlusOne
      <3>6. Cardinality(c..n) = n-c+1
        BY <2>1, <3>1 DEF P
      <3>7. IsFiniteSet(c..(n+1))
        BY <3>3, <3>5
      <3>8. Cardinality(c..(n+1)) = Cardinality(c..n) + 1
        BY <3>3, <3>5
      <3>9. Cardinality(c..(n+1)) = (n-c+1) + 1
        BY <3>6, <3>8
      <3>10. (n-c+1) + 1 = n+1-c+1
        BY SMT
      <3>11. Cardinality(c..(n+1)) = n+1-c+1
        BY <3>9, <3>10
      <3>12. QED
        BY <2>4, <3>7, <3>11, SMT
    <2>5. c > n+1 \/ c = n+1 \/ c < n+1
      BY SMT
    <2>6. QED
      BY <2>2, <2>3, <2>4, <2>5
  <1>3. \A n \in Nat : P(n)
    BY <1>1, <1>2, NatInduction
  <1>4. P(b)
    BY <1>3
  <1>5. QED
    BY <1>4 DEF P

=============================================================================
