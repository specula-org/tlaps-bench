---- MODULE Consensus_IsBijectionInverse ----
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
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
  PROOF OMITTED

-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
PROOF
  <1>0. DEFINE g == [y \in T |-> CHOOSE x \in S : f[x] = y]
  <1>1. \A y \in T : /\ g[y] \in S
                       /\ f[g[y]] = y
    PROOF
      <2>1. SUFFICES ASSUME NEW y \in T
                       PROVE  /\ g[y] \in S
                               /\ f[g[y]] = y
        OBVIOUS
      <2>2. \E x \in S : f[x] = y
        BY DEF IsBijection
      <2>3. g[y] = CHOOSE x \in S : f[x] = y
        BY DEF g
      <2> QED BY <2>2, <2>3
  <1>2. g \in [T -> S]
    BY <1>1 DEF g
  <1>3. \A y1, y2 \in T : (y1 # y2) => (g[y1] # g[y2])
    PROOF
      <2>1. SUFFICES ASSUME NEW y1 \in T, NEW y2 \in T
                       PROVE  (y1 # y2) => (g[y1] # g[y2])
        OBVIOUS
      <2>2. ASSUME y1 # y2
             PROVE  g[y1] # g[y2]
        PROOF
          <3>1. f[g[y1]] = y1 /\ f[g[y2]] = y2
            BY <1>1
          <3> QED BY <2>2, <3>1
      <2> QED BY <2>2
  <1>4. \A x \in S : \E y \in T : g[y] = x
    PROOF
      <2>1. SUFFICES ASSUME NEW x \in S
                       PROVE  \E y \in T : g[y] = x
        OBVIOUS
      <2>2. f[x] \in T
        BY DEF IsBijection
      <2>3. /\ g[f[x]] \in S
             /\ f[g[f[x]]] = f[x]
        BY <1>1, <2>2
      <2>4. g[f[x]] = x
        BY <2>3 DEF IsBijection
      <2> QED BY <2>2, <2>4
  <1>5. IsBijection(g, T, S)
    BY <1>2, <1>3, <1>4 DEF IsBijection
  <1> QED BY <1>5

========================================
