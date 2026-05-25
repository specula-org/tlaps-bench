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

  
------------------------------------------------------------------



------------------------------------------------------------------




------------------------------------------------------------------


-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T,
         IsBijection(f, S, T)
  PROVE  \E g : IsBijection(g, T, S)
PROOF
<1> DEFINE Inv == [y \in T |-> CHOOSE x \in S : f[x] = y]
<1>1. f \in [S -> T]
  BY DEF IsBijection
<1>2. \A a, b \in S : (a # b) => (f[a] # f[b])
  BY DEF IsBijection
<1>3. \A y \in T : \E x \in S : f[x] = y
  BY DEF IsBijection
<1>4. \A y \in T : Inv[y] \in S /\ f[Inv[y]] = y
  <2> SUFFICES ASSUME NEW y \in T
               PROVE  Inv[y] \in S /\ f[Inv[y]] = y
    OBVIOUS
  <2>1. \E x \in S : f[x] = y
    BY <1>3
  <2>2. Inv[y] = CHOOSE x \in S : f[x] = y
    BY DEF Inv
  <2> QED
    BY <2>1, <2>2
<1>5. Inv \in [T -> S]
  BY <1>4
<1>6. \A y, z \in T : (y # z) => (Inv[y] # Inv[z])
  <2> SUFFICES ASSUME NEW y \in T, NEW z \in T, y # z, Inv[y] = Inv[z]
               PROVE  FALSE
    OBVIOUS
  <2>1. f[Inv[y]] = y /\ f[Inv[z]] = z
    BY <1>4
  <2> QED
    BY <2>1
<1>7. \A x \in S : \E y \in T : Inv[y] = x
  <2> SUFFICES ASSUME NEW x \in S
               PROVE  \E y \in T : Inv[y] = x
    OBVIOUS
  <2>1. f[x] \in T
    BY <1>1
  <2>2. Inv[f[x]] \in S /\ f[Inv[f[x]]] = f[x]
    BY <1>4, <2>1
  <2>3. Inv[f[x]] = x
    BY <2>2, <1>2
  <2> QED
    BY <2>1, <2>3
<1>8. IsBijection(Inv, T, S)
  BY <1>5, <1>6, <1>7 DEF IsBijection
<1> QED
  <2> WITNESS Inv
  <2> QED
    BY <1>8





-------------------------------------------------------


-----------------------------------------------------------------------------

-------------------------------------------------------



=============================================================================
