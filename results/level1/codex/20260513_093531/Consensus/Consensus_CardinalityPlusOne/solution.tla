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
  <1> DEFINE c == Cardinality(S)
  <1>1. c \in Nat
    BY CardinalityInNat
  <1>2. \E f : IsBijection(f, 1..c, S)
    BY <1>1, CardinalityAxiom DEF c
  <1>3. PICK f : IsBijection(f, 1..c, S)
    BY <1>2
  <1>4. \E g : IsBijection(g, 1..(c + 1), S \cup {x})
    PROOF
      <2> DEFINE g == [i \in 1..(c + 1) |-> IF i = c + 1 THEN x ELSE f[i]]
      <2>1. g \in [1..(c + 1) -> S \cup {x}]
        BY <1>1, <1>3 DEF g, IsBijection
      <2>2. \A i, j \in 1..(c + 1) : (i # j) => (g[i] # g[j])
        BY <1>1, <1>3, x \notin S DEF g, IsBijection
      <2>3. \A y \in S \cup {x} : \E i \in 1..(c + 1) : g[i] = y
        BY <1>1, <1>3, x \notin S DEF g, IsBijection
      <2>4. IsBijection(g, 1..(c + 1), S \cup {x})
        BY <2>1, <2>2, <2>3 DEF IsBijection
      <2> QED
        BY <2>4
    
  <1>5. IsFiniteSet(S \cup {x})
    BY <1>1, <1>4 DEF IsFiniteSet
  <1>6. Cardinality(S \cup {x}) = c + 1
    BY <1>1, <1>4, <1>5, CardinalityAxiom
  <1> QED
    BY <1>5, <1>6 DEF c

========================================
