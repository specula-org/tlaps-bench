---- MODULE Consensus_CardinalityPlusOne ----
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
  <1>2. \E f : IsBijection(f, 1..Cardinality(S), S)
    BY CardinalityAxiom, <1>1 DEF IsFiniteSet
  <1>3. PICK f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>2
  <1>4. DEFINE n == Cardinality(S)
  <1>5. DEFINE g == [i \in 1..(n+1) |-> IF i \in 1..n THEN f[i] ELSE x]
  <1>6. IsBijection(g, 1..(n+1), S \cup {x})
  PROOF
    <2>1. g \in [1..(n+1) -> S \cup {x}]
      BY <1>3 DEF IsBijection, g, n
    <2>2. \A i, j \in 1..(n+1) : (i # j) => (g[i] # g[j])
    PROOF
      <3>1. SUFFICES ASSUME NEW i \in 1..(n+1),
                            NEW j \in 1..(n+1),
                            i # j
                     PROVE g[i] # g[j]
        OBVIOUS
      <3>2. CASE i \in 1..n /\ j \in 1..n
        BY <1>3, <3>1, <3>2 DEF IsBijection, g
      <3>3. CASE i \in 1..n /\ j \notin 1..n
        BY <1>3, <3>1, <3>3 DEF IsBijection, g, n
      <3>4. CASE i \notin 1..n /\ j \in 1..n
        BY <1>3, <3>1, <3>4 DEF IsBijection, g, n
      <3>5. CASE i \notin 1..n /\ j \notin 1..n
        BY <1>1, <3>1, <3>5
      <3>6. QED
        BY <3>2, <3>3, <3>4, <3>5
    <2>3. \A y \in S \cup {x} : \E i \in 1..(n+1) : g[i] = y
    PROOF
      <3>1. SUFFICES ASSUME NEW y \in S \cup {x}
                     PROVE \E i \in 1..(n+1) : g[i] = y
        OBVIOUS
      <3>2. CASE y \in S
      PROOF
        <4>1. \E i \in 1..n : f[i] = y
          BY <1>3, <3>1, <3>2 DEF IsBijection
        <4>2. PICK i \in 1..n : f[i] = y
          BY <4>1
        <4>3. i \in 1..(n+1)
          BY <1>1, <4>2
        <4>4. g[i] = y
          BY <4>2, <4>3 DEF g
        <4>5. QED
          BY <4>3, <4>4
      <3>3. CASE y \notin S
      PROOF
        <4>1. y = x
          BY <3>1, <3>3
        <4>2. n+1 \in 1..(n+1)
          BY <1>1
        <4>3. n+1 \notin 1..n
          BY <1>1
        <4>4. g[n+1] = y
          BY <4>1, <4>2, <4>3 DEF g
        <4>5. QED
          BY <4>2, <4>4
      <3>4. QED
        BY <3>1, <3>2, <3>3
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF IsBijection
  <1>7. IsFiniteSet(S \cup {x})
    BY <1>1, <1>6 DEF IsFiniteSet
  <1>8. Cardinality(S \cup {x}) = n+1
    BY CardinalityAxiom, <1>1, <1>6, <1>7
  <1>9. QED
    BY <1>7, <1>8

========================================
