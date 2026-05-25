-------------------------------- MODULE Sets_IsBijectionTransitive --------------------------------
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


THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U,
           IsBijection(f1, S, U),
           IsBijection(f2, U, T)
  PROVE  \E g : IsBijection(g, S, T)
<1> DEFINE g == [x \in S |-> f2[f1[x]]]
<1>1 g \in [S -> T]
  <2>1 \A x \in S : f1[x] \in U
    BY DEF IsBijection
  <2>2 \A x \in S : f2[f1[x]] \in T
    BY <2>1 DEF IsBijection
  <2> QED
    BY <2>2
<1>2 \A x, y \in S : (x # y) => (g[x] # g[y])
  <2> TAKE x, y \in S
  <2> HAVE x # y
  <2>1 f1[x] # f1[y]
    BY DEF IsBijection
  <2>2 f1[x] \in U /\ f1[y] \in U
    BY DEF IsBijection
  <2>3 f2[f1[x]] # f2[f1[y]]
    BY <2>1, <2>2 DEF IsBijection
  <2>4 g[x] = f2[f1[x]] /\ g[y] = f2[f1[y]]
    OBVIOUS
  <2> QED
    BY <2>3, <2>4
<1>3 \A z \in T : \E x \in S : g[x] = z
  <2> TAKE z \in T
  <2>1 PICK u \in U : f2[u] = z
    BY DEF IsBijection
  <2>2 PICK x \in S : f1[x] = u
    BY <2>1 DEF IsBijection
  <2>3 g[x] = z
    BY <2>1, <2>2
  <2> QED
    BY <2>3
<1>4 IsBijection(g, S, T)
  BY <1>1, <1>2, <1>3 DEF IsBijection
<1> QED
  BY <1>4




-------------------------------------------------------


-----------------------------------------------------------------------------

-------------------------------------------------------



=============================================================================
