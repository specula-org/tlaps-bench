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
<1>NDef. DEFINE n == Cardinality(S)
<1>NNat. n \in Nat BY CardinalityInNat DEF n
<1>PickG. PICK g : IsBijection(g, 1..n, S)
  BY CardinalityAxiom DEF n
<1>HDef. DEFINE h == [i \in 1..(n+1) |-> IF i = n+1 THEN x ELSE g[i]]
<1>HBij. IsBijection(h, 1..(n+1), S \cup {x})
  <2>1. h \in [1..(n+1) -> S \cup {x}]
    BY <1>NNat, <1>PickG DEF h, IsBijection
  <2>2. \A i, j \in 1..(n+1) : (i # j) => (h[i] # h[j])
    <3>. SUFFICES ASSUME NEW i \in 1..(n+1), NEW j \in 1..(n+1), i # j
                 PROVE h[i] # h[j]
      BY <1>NNat, <1>PickG DEF h, IsBijection
    <3>IIn. i \in 1..(n+1) OBVIOUS
    <3>JIn. j \in 1..(n+1) OBVIOUS
    <3>Neq. i # j OBVIOUS
    <3>1. CASE i = n+1
      <4>1. j \in 1..n BY <3>1, <3>JIn, <3>Neq, <1>NNat
      <4>2. h[i] = x BY <3>1 DEF h
      <4>3. h[j] = g[j] BY <3>1, <3>Neq DEF h
      <4>4. g[j] \in S BY <1>PickG, <4>1 DEF IsBijection
      <4>. QED BY <4>2, <4>3, <4>4
    <3>2. CASE j = n+1
      <4>1. i \in 1..n BY <3>IIn, <3>2, <3>Neq, <1>NNat
      <4>2. h[j] = x BY <3>2 DEF h
      <4>3. h[i] = g[i] BY <3>2, <3>Neq DEF h
      <4>4. g[i] \in S BY <1>PickG, <4>1 DEF IsBijection
      <4>. QED BY <4>2, <4>3, <4>4
    <3>3. CASE i # n+1 /\ j # n+1
      <4>1. i \in 1..n /\ j \in 1..n BY <3>IIn, <3>JIn, <3>3, <1>NNat
      <4>2. h[i] = g[i] /\ h[j] = g[j] BY <3>3 DEF h
      <4>3. g[i] # g[j] BY <1>PickG, <3>Neq, <4>1 DEF IsBijection
      <4>. QED BY <4>2, <4>3
    <3>. QED BY <3>1, <3>2, <3>3
  <2>3. \A y \in S \cup {x} : \E i \in 1..(n+1) : h[i] = y
    <3>. SUFFICES ASSUME NEW y \in S \cup {x}
                 PROVE \E i \in 1..(n+1) : h[i] = y
      OBVIOUS
    <3>YIn. y \in S \cup {x} OBVIOUS
    <3>1. CASE y = x
      <4>1. n+1 \in 1..(n+1) BY <1>NNat
      <4>2. h[n+1] = IF n+1 = n+1 THEN x ELSE g[n+1]
        BY <4>1 DEF h
      <4>3. h[n+1] = x BY <4>2
      <4>4. h[n+1] = y BY <3>1, <4>3
      <4>. QED BY <4>1, <4>4
    <3>2. CASE y # x
      <4>1. y \in S BY <3>YIn, <3>2
      <4>2. PICK i \in 1..n : g[i] = y BY <1>PickG, <4>1 DEF IsBijection
      <4>3. i \in 1..(n+1) BY <1>NNat, <4>2
      <4>4. i # n+1 BY <1>NNat, <4>2
      <4>5. h[i] = IF i = n+1 THEN x ELSE g[i]
        BY <4>3 DEF h
      <4>6. h[i] = y BY <4>2, <4>4, <4>5
      <4>. QED BY <4>3, <4>6
    <3>. QED BY <3>1, <3>2
  <2>. QED BY <2>1, <2>2, <2>3 DEF IsBijection
<1>1. IsFiniteSet(S \cup {x})
  BY <1>NNat, <1>HBij DEF IsFiniteSet
<1>CardEq. Cardinality(S \cup {x}) = n + 1
  BY <1>1, <1>NNat, <1>HBij, CardinalityAxiom
<1>. QED BY <1>1, <1>CardEq DEF n

========================================
