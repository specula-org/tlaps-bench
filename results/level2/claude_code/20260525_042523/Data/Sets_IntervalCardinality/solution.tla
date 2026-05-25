-------------------------------- MODULE Sets_IntervalCardinality --------------------------------
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

  
------------------------------------------------------------------



------------------------------------------------------------------



IntervalCard(a, b) == IF a > b THEN 0 ELSE b-a+1
IntervalFcn(a, b) == [i \in 1..IntervalCard(a, b) |-> a + i - 1]

THEOREM IntervalCardinality ==
  ASSUME NEW a \in Nat, NEW b \in Nat
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
<1> DEFINE m == IntervalCard(a, b)
<1> DEFINE f == IntervalFcn(a, b)
<1>1. m \in Nat
  BY DEF IntervalCard
<1>2. \A i \in 1..m : a + i - 1 \in a..b
  BY DEF IntervalCard
<1>3. f \in [1..m -> a..b]
  BY <1>2 DEF IntervalFcn
<1>4. \A x, y \in 1..m : (x # y) => (f[x] # f[y])
  BY DEF IntervalFcn
<1>5. \A y \in a..b : \E x \in 1..m : f[x] = y
  <2>1. TAKE y \in a..b
  <2>2. (y - a + 1) \in 1..m
    BY DEF IntervalCard
  <2>3. f[y - a + 1] = y
    BY <2>2 DEF IntervalFcn
  <2>4. QED
    BY <2>2, <2>3
<1>6. IsBijection(f, 1..m, a..b)
  BY <1>3, <1>4, <1>5 DEF IsBijection
<1>7. IsFiniteSet(a..b)
  BY <1>1, <1>6 DEF IsFiniteSet
<1>8. m = IF a > b THEN 0 ELSE b-a+1
  BY DEF IntervalCard
<1>9. Cardinality(a..b) = m
  BY <1>1, <1>6, <1>7, CardinalityAxiom
<1> QED
  BY <1>7, <1>8, <1>9

------------------------------------------------------------------


-----------------------------------------------------------------------------






-------------------------------------------------------


-----------------------------------------------------------------------------

-------------------------------------------------------



=============================================================================
