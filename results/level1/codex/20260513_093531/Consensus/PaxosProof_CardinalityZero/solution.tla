---- MODULE PaxosProof_CardinalityZero ----
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
PROOF
  <1>1. IsFiniteSet({})
  PROOF
    <2>1. IsBijection([x \in {} |-> x], 1..0, {})
      BY DEF IsBijection
    <2>2. 0 \in Nat
      OBVIOUS
    <2>3. QED BY <2>1, <2>2 DEF IsFiniteSet
  <1>2. Cardinality({}) = 0
    BY <1>1, CardinalityAxiom DEF IsFiniteSet, IsBijection
  <1>3. \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
    BY CardinalityAxiom DEF IsFiniteSet, IsBijection
  <1> QED BY <1>1, <1>2, <1>3

========================================
