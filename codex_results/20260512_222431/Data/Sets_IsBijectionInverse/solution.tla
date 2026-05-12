-------------------------------- MODULE Sets_IsBijectionInverse --------------------------------
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
  <1> DEFINE g == [y \in T |-> CHOOSE x \in S : f[x] = y]
  <1>1. g \in [T -> S]
  PROOF
    <2>1. \A y \in T : g[y] \in S
    PROOF
      <3>1. TAKE y \in T
      <3>2. \E x \in S : f[x] = y BY <3>1 DEF IsBijection
      <3>3. g[y] \in S BY <3>2 DEF g
      <3> QED BY <3>3
    <2> QED BY <2>1 DEF g
  <1>2. \A y1, y2 \in T : (y1 # y2) => (g[y1] # g[y2])
  PROOF
    <2>1. TAKE y1 \in T, y2 \in T
    <2>2. SUFFICES ASSUME y1 # y2 PROVE g[y1] # g[y2] OBVIOUS
    <2>3. \E x \in S : f[x] = y1 BY <2>1 DEF IsBijection
    <2>4. \E x \in S : f[x] = y2 BY <2>1 DEF IsBijection
    <2>5. g[y1] \in S /\ f[g[y1]] = y1 BY <2>3 DEF g
    <2>6. g[y2] \in S /\ f[g[y2]] = y2 BY <2>4 DEF g
    <2>7. g[y1] # g[y2]
      BY <2>2, <2>5, <2>6 DEF IsBijection
    <2> QED BY <2>7
  <1>3. \A x \in S : \E y \in T : g[y] = x
  PROOF
    <2>1. TAKE x \in S
    <2>2. f[x] \in T BY <2>1 DEF IsBijection
    <2>3. \E xx \in S : f[xx] = f[x] BY <2>1
    <2>4. g[f[x]] \in S /\ f[g[f[x]]] = f[x] BY <2>3, <2>2 DEF g
    <2>5. g[f[x]] = x BY <2>1, <2>4 DEF IsBijection
    <2>6. \E y \in T : g[y] = x BY <2>2, <2>5
    <2> QED BY <2>6
  <1>4. IsBijection(g, T, S) BY <1>1, <1>2, <1>3 DEF IsBijection
  <1> QED BY <1>4

=============================================================================
