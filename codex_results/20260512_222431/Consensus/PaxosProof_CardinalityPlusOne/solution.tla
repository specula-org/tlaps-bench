---- MODULE PaxosProof_CardinalityPlusOne ----
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
<1>. DEFINE n == Cardinality(S)
<1>1. n \in Nat
  BY CardinalityInNat DEF n
<1>2. \E f : IsBijection(f, 1..n, S)
  BY <1>1, CardinalityAxiom DEF n
<1>3. PICK F : IsBijection(F, 1..n, S)
  BY <1>2
<1>4. F \in [1..n -> S]
  BY <1>3 DEF IsBijection
<1>5. \A i, j \in 1..n : (i # j) => (F[i] # F[j])
  BY <1>3 DEF IsBijection
<1>6. \A y \in S : \E i \in 1..n : F[i] = y
  BY <1>3 DEF IsBijection
<1>. DEFINE G == [i \in 1..(n+1) |-> IF i <= n THEN F[i] ELSE x]
<1>7. G \in [1..(n+1) -> S \cup {x}]
  BY <1>1, <1>4, SMT DEF G
<1>8. \A i, j \in 1..(n+1) : (i # j) => (G[i] # G[j])
  BY <1>1, <1>4, <1>5, SMT DEF G
<1>9. \A y \in S \cup {x} : \E i \in 1..(n+1) : G[i] = y
  BY <1>1, <1>6, SMT DEF G
<1>10. IsBijection(G, 1..(n+1), S \cup {x})
  BY <1>7, <1>8, <1>9 DEF IsBijection
<1>11. IsFiniteSet(S \cup {x})
  BY <1>1, <1>10 DEF IsFiniteSet
<1>12. Cardinality(S \cup {x}) = n + 1
  BY <1>1, <1>10, <1>11, CardinalityAxiom
<1>13. Cardinality(S \cup {x}) = Cardinality(S) + 1
  BY <1>12 DEF n
<1> QED
  BY <1>11, <1>13

========================================
