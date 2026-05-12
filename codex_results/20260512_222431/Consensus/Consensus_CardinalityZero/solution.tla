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
<1>1. IsBijection([x \in {} |-> x], 1..0, {})
  BY DEF IsBijection
<1>2. IsFiniteSet({})
  BY <1>1 DEF IsFiniteSet
<1>3. 0 \in Nat /\ \E f : IsBijection(f, 1..0, {})
  BY <1>1
<1>4. Cardinality({}) = 0
  BY CardinalityAxiom, <1>2, <1>3
<1>5. ASSUME NEW S,
              IsFiniteSet(S) /\ (Cardinality(S)=0)
       PROVE  S = {}
  <2>1. 0 = Cardinality(S)
    BY <1>5
  <2>2. \E f : IsBijection(f, 1..0, S)
    BY CardinalityAxiom, <1>5, <2>1
  <2>3. PICK f : IsBijection(f, 1..0, S)
    BY <2>2
  <2>4. \A y \in S : \E x \in 1..0 : f[x] = y
    BY <2>3 DEF IsBijection
  <2>. QED BY <2>4
<1>6. \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
  BY <1>5
<1>7. QED BY <1>2, <1>4, <1>6

========================================
