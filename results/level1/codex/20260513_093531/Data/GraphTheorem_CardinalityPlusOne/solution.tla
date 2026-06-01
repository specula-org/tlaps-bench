---- MODULE GraphTheorem_CardinalityPlusOne ----
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
PROOF
  <1>1. Cardinality(S) \in Nat
    BY CardinalityInNat
  <1>2. x \notin S
    OBVIOUS
  <1>3. \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>1, CardinalityAxiom DEF IsFiniteSet
  <1>4. DEFINE n == Cardinality(S)
  <1>5. n \in Nat
    BY <1>1 DEF n
  <1>6. \E g : IsBijection(g, 1..(n+1), S \cup {x})
  PROOF
    <2>1. n \in Nat
      BY <1>5
    <2>2. \E f : IsBijection(f, 1..n, S)
      BY <1>3
    <2>3. PICK f : IsBijection(f, 1..n, S)
      BY <2>2
    <2>4. f \in [1..n -> S]
      BY <2>3 DEF IsBijection
    <2>5. \A y \in S : \E i \in 1..n : f[i] = y
      BY <2>3 DEF IsBijection
    <2>6. \A i, j \in 1..n : (i # j) => (f[i] # f[j])
      BY <2>3 DEF IsBijection
    <2>7. DEFINE g == [i \in 1..(n+1) |-> IF i <= n THEN f[i] ELSE x]
    <2>8. g \in [1..(n+1) -> S \cup {x}]
      BY SMT, <2>1, <2>4 DEF g
    <2>9. ASSUME NEW y \in S \cup {x}
           PROVE  \E i \in 1..(n+1) : g[i] = y
      BY Z3, <2>1, <2>5 DEF g
    <2>10. ASSUME NEW i \in 1..(n+1), NEW j \in 1..(n+1), i # j
            PROVE  g[i] # g[j]
    PROOF
      <3>1. CASE i # n+1 /\ j # n+1
      PROOF
        <4>1. i \in 1..n /\ j \in 1..n
          BY <2>1, <2>10, <3>1
        <4>2. f[i] # f[j]
          BY <2>6, <2>10, <4>1
        <4>3. g[i] = f[i] /\ g[j] = f[j]
          BY <2>1, <2>10, <3>1 DEF g
        <4>4. QED
          BY <4>2, <4>3
      <3>2. CASE i # n+1 /\ j = n+1
      PROOF
        <4>1. i \in 1..n
          BY <2>1, <2>10, <3>2
        <4>2. f[i] \in S
          BY <2>4, <4>1
        <4>3. g[i] = f[i] /\ g[j] = x
          BY <2>1, <2>10, <3>2 DEF g
        <4>4. QED
          BY <1>2, <4>2, <4>3
      <3>3. CASE i = n+1 /\ j # n+1
      PROOF
        <4>1. j \in 1..n
          BY <2>1, <2>10, <3>3
        <4>2. f[j] \in S
          BY <2>4, <4>1
        <4>3. g[i] = x /\ g[j] = f[j]
          BY <2>1, <2>10, <3>3 DEF g
        <4>4. QED
          BY <1>2, <4>2, <4>3
      <3>4. CASE i = n+1 /\ j = n+1
        BY <2>1, <2>10, <3>4
      <3>5. QED
        BY <2>1, <2>10, <3>1, <3>2, <3>3, <3>4
    <2>11. IsBijection(g, 1..(n+1), S \cup {x})
      BY <2>8, <2>9, <2>10 DEF IsBijection
    <2>12. QED
      BY <2>11
  <1>7. IsFiniteSet(S \cup {x})
    BY <1>1, <1>6 DEF IsFiniteSet
  <1>8. Cardinality(S \cup {x}) = Cardinality(S) + 1
    BY <1>5, <1>6, <1>7, CardinalityAxiom DEF IsFiniteSet, n
  <1>9. QED
    BY <1>7, <1>8

========================================
