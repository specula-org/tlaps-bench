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
  <1> DEFINE P(n) == /\ IsFiniteSet(a..n)
                       /\ Cardinality(a..n) = IF a > n THEN 0 ELSE n-a+1
  <1>1. P(0)
    <2>1. CASE a = 0
      <3>1. a..0 = {0} BY <2>1, SMT
      <3>2. QED BY <2>1, <3>1, CardinalityOne DEF P
    <2>2. CASE a # 0
      <3>1. a > 0 BY <2>2, SMT
      <3>2. a..0 = {} BY <3>1, SMT
      <3>3. QED BY <3>1, <3>2, CardinalityZero DEF P
    <2> QED BY <2>1, <2>2
  <1>2. \A n \in Nat : P(n) => P(n+1)
    <2> SUFFICES ASSUME NEW n \in Nat, P(n)
                 PROVE P(n+1)
      OBVIOUS
    <2>1. IsFiniteSet(a..n) BY DEF P
    <2>2. CASE a > n+1
      <3>1. a..(n+1) = {} BY <2>2, SMT
      <3>2. QED BY <2>2, <3>1, CardinalityZero DEF P
    <2>3. CASE a = n+1
      <3>1. a..n = {} BY <2>3, SMT
      <3>2. n+1 \notin a..n BY <3>1
      <3>3. a..(n+1) = (a..n) \cup {n+1} BY <2>3, SMT
      <3>4. /\ IsFiniteSet((a..n) \cup {n+1})
             /\ Cardinality((a..n) \cup {n+1}) = Cardinality(a..n) + 1
        BY <2>1, <3>2, CardinalityPlusOne
      <3>5. /\ IsFiniteSet(a..(n+1))
             /\ Cardinality(a..(n+1)) = Cardinality(a..n) + 1
        BY <3>3, <3>4
      <3>6. Cardinality(a..n) = 0 BY <2>3, <3>1, CardinalityZero
      <3>7. QED BY <2>3, <3>5, <3>6 DEF P
    <2>4. CASE a < n+1
      <3>1. a <= n BY <2>4, SMT
      <3>2. n+1 \notin a..n BY SMT
      <3>3. a..(n+1) = (a..n) \cup {n+1} BY <3>1, SMT
      <3>4. /\ IsFiniteSet((a..n) \cup {n+1})
             /\ Cardinality((a..n) \cup {n+1}) = Cardinality(a..n) + 1
        BY <2>1, <3>2, CardinalityPlusOne
      <3>5. /\ IsFiniteSet(a..(n+1))
             /\ Cardinality(a..(n+1)) = Cardinality(a..n) + 1
        BY <3>3, <3>4
      <3>6. ~(a > n) BY <3>1, SMT
      <3>7. Cardinality(a..n) = n-a+1 BY <3>6 DEF P
      <3>8. QED BY <2>4, <3>5, <3>7 DEF P
    <2> QED BY <2>2, <2>3, <2>4, SMT
  <1>3. \A n \in Nat : P(n) BY <1>1, <1>2, NatInduction
  <1> QED BY <1>3 DEF P

=============================================================================
