-------------------------------- MODULE Sets_FiniteSubset --------------------------------
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
  PROOF OMITTED

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
  PROOF OMITTED

THEOREM IsBijectionCardinality ==
  \A f, S, T : /\ IsFiniteSet(S)
               /\ IsFiniteSet(T)
               => (IsBijection(f, S, T) <=> Cardinality(S) = Cardinality(T))

LEMMA CardinalitySetMinus ==
      ASSUME NEW S, IsFiniteSet(S),
             NEW x \in S
      PROVE /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1
  PROOF OMITTED

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
PROOF
  <1>. DEFINE Q(n) == \A U : /\ IsFiniteSet(U)
                              /\ Cardinality(U) = n
                              => \A V : V \subseteq U
                                       => /\ IsFiniteSet(V)
                                          /\ Cardinality(V) \leq Cardinality(U)
  <1>1. Q(0)
    <2>1. SUFFICES ASSUME NEW U,
                          IsFiniteSet(U),
                          Cardinality(U) = 0,
                          NEW V,
                          V \subseteq U
                   PROVE  /\ IsFiniteSet(V)
                          /\ Cardinality(V) \leq Cardinality(U)
      OBVIOUS
    <2>2. U = {}  BY <2>1, CardinalityZero
    <2>3. V = {}  BY <2>1, <2>2
    <2>4. /\ IsFiniteSet(V)
           /\ Cardinality(V) = 0
      BY <2>3, CardinalityZero
    <2> QED BY <2>1, <2>4
  <1>2. ASSUME NEW n \in Nat, Q(n) PROVE Q(n+1)
    <2>1. SUFFICES ASSUME NEW U,
                          IsFiniteSet(U),
                          Cardinality(U) = n+1,
                          NEW V,
                          V \subseteq U
                   PROVE  /\ IsFiniteSet(V)
                          /\ Cardinality(V) \leq Cardinality(U)
      OBVIOUS
    <2>2. CASE V = U
      <3>1. Cardinality(V) = Cardinality(U)
        BY <2>1, <2>2
      <3> QED BY <2>1, <2>2, <3>1
    <2>3. CASE V # U
      <3>1. PICK x \in U : x \notin V
        BY <2>1, <2>3
      <3>2. /\ IsFiniteSet(U \ {x})
             /\ Cardinality(U \ {x}) = Cardinality(U) - 1
        BY <2>1, <3>1, CardinalitySetMinus
      <3>3. Cardinality(U \ {x}) = n
        BY <2>1, <3>2
      <3>4. V \subseteq U \ {x}
        BY <2>1, <3>1
      <3>5. /\ IsFiniteSet(V)
             /\ Cardinality(V) \leq Cardinality(U \ {x})
        BY <1>2, <3>2, <3>3, <3>4 DEF Q
      <3>6. Cardinality(U \ {x}) \leq Cardinality(U)
        BY <2>1, <3>2
      <3>6a. /\ Cardinality(V) \in Nat
              /\ Cardinality(U \ {x}) \in Nat
              /\ Cardinality(U) \in Nat
        BY <2>1, <3>2, <3>5, CardinalityInNat
      <3>7. Cardinality(V) \leq Cardinality(U)
        BY <3>5, <3>6, <3>6a, SMT
      <3> QED BY <3>5, <3>7
    <2> QED BY <2>2, <2>3
  <1>3. Cardinality(TT) \in Nat
    BY CardinalityInNat
  <1>4. \A n \in Nat : Q(n) => Q(n+1)
    <2>1. SUFFICES ASSUME NEW n \in Nat, Q(n)
                   PROVE  Q(n+1)
      OBVIOUS
    <2> QED BY <1>2, <2>1
  <1>5. \A n \in Nat : Q(n)
    <2>. HIDE DEF Q
    <2>. QED BY <1>1, <1>4, NatInduction, Isa
  <1> QED BY <1>3, <1>5 DEF Q

=============================================================================
