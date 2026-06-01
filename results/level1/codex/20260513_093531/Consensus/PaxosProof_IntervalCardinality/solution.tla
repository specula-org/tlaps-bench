---- MODULE PaxosProof_IntervalCardinality ----
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
PROOF
  <1> DEFINE P(n) == /\ IsFiniteSet(a..n)
                    /\ Cardinality(a..n) = IF a > n THEN 0 ELSE n-a+1
  <1>1. P(0)
  PROOF
    <2>1. CASE a = 0
    PROOF
      <3>1. a..0 = {0} BY <2>1
      <3>2. QED BY <2>1, <3>1, CardinalityOne DEF P
    <2>2. CASE a # 0
    PROOF
      <3>1. a > 0 BY <2>2
      <3>2. a..0 = {} BY <3>1
      <3>3. QED BY <3>1, <3>2, CardinalityZero DEF P
    <2>3. QED BY <2>1, <2>2
  <1>2. \A n \in Nat : P(n) => P(n+1)
  PROOF
    <2>1. SUFFICES ASSUME NEW n \in Nat, P(n)
            PROVE  P(n+1)
      OBVIOUS
    <2>2. CASE a > n+1
    PROOF
      <3>1. a..(n+1) = {} BY <2>2
      <3>2. QED BY <2>2, <3>1, CardinalityZero DEF P
    <2>3. CASE ~(a > n+1)
    PROOF
      <3>1. CASE a = n+1
      PROOF
        <4>1. a..(n+1) = {n+1} BY <3>1
        <4>2. QED BY <3>1, <4>1, CardinalityOne DEF P
      <3>2. CASE a # n+1
      PROOF
        <4>1. a <= n BY <2>1, <2>3, <3>2
        <4>2. a..(n+1) = (a..n) \cup {n+1} BY <4>1
        <4>3. n+1 \notin a..n BY <2>1
        <4>4. /\ IsFiniteSet((a..n) \cup {n+1})
               /\ Cardinality((a..n) \cup {n+1}) = Cardinality(a..n) + 1
          BY <2>1, <4>3, CardinalityPlusOne DEF P
        <4>5. Cardinality(a..n) = n-a+1 BY <2>1, <4>1 DEF P
        <4>6. IsFiniteSet(a..(n+1)) BY <4>2, <4>4
        <4>7. Cardinality(a..(n+1)) = Cardinality(a..n) + 1
          BY <4>2, <4>4
        <4>8. Cardinality(a..(n+1)) = (n+1)-a+1
          BY <2>1, <4>5, <4>7
        <4>9. QED BY <2>3, <4>6, <4>8 DEF P
      <3>3. QED BY <3>1, <3>2
    <2>4. QED BY <2>2, <2>3
  <1>3. \A n \in Nat : P(n) BY <1>1, <1>2, NatInduction
  <1>4. P(b) BY <1>3
  <1>5. QED BY <1>4 DEF P

========================================
