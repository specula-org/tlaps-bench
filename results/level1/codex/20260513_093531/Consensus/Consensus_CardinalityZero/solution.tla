---- MODULE Consensus_CardinalityZero ----
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
  <1>1. 1..0 = {} BY DEF Nat
  <1>2. IsFiniteSet({})
    BY <1>1 DEF IsFiniteSet, IsBijection
  <1>3. Cardinality({}) = 0
    BY <1>2, CardinalityAxiom DEF IsFiniteSet, IsBijection
  <1>4. \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
  PROOF
    <2>1. TAKE S
    <2>2. ASSUME IsFiniteSet(S) /\ (Cardinality(S)=0)
            PROVE S = {}
    PROOF
      <3>1. (0 \in Nat) /\ \E f : IsBijection(f, 1..0, S)
        BY <2>2, CardinalityAxiom
      <3>2. \E f : IsBijection(f, 1..0, S) BY <3>1
      <3>3. PICK f : IsBijection(f, 1..0, S) BY <3>2
      <3>4. \A y \in S : \E x \in 1..0 : f[x] = y
        BY <3>3 DEF IsBijection
      <3>5. S = {}
        BY <1>1, <3>4
      <3> QED BY <3>5
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3, <1>4

========================================
