-------------------------------- MODULE Sets_CardinalityTwo --------------------------------
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


LEMMA Range12 == 1..2 = {1, 2}
  BY SMT

THEOREM CardinalityTwo == \A m, p : m # p =>
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
<1>1. TAKE m, p
<1>2. SUFFICES ASSUME m # p
               PROVE  /\ IsFiniteSet({m,p})
                      /\ Cardinality({m,p}) = 2
      OBVIOUS
<1> DEFINE f == [i \in 1..2 |-> IF i = 1 THEN m ELSE p]
<1>3. IsBijection(f, 1..2, {m,p})
  <2>1. f \in [1..2 -> {m,p}]
    OBVIOUS
  <2>2. \A x, y \in 1..2 : (x # y) => (f[x] # f[y])
    BY <1>2, Range12
  <2>3. \A y \in {m,p} : \E x \in 1..2 : f[x] = y
    BY Range12
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF IsBijection
<1>4. IsFiniteSet({m,p})
  <2>1. 2 \in Nat
    OBVIOUS
  <2>2. QED
    BY <1>3, <2>1 DEF IsFiniteSet
<1>5. Cardinality({m,p}) = 2
  <2>1. 2 \in Nat
    OBVIOUS
  <2>2. \E g : IsBijection(g, 1..2, {m,p})
    BY <1>3
  <2>3. QED
    BY <1>4, <2>1, <2>2, CardinalityAxiom
<1>6. QED
  BY <1>4, <1>5


------------------------------------------------------------------


-----------------------------------------------------------------------------






-------------------------------------------------------


-----------------------------------------------------------------------------

-------------------------------------------------------



=============================================================================
