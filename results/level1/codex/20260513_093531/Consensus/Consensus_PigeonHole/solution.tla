---- MODULE Consensus_PigeonHole ----
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
  PROOF OMITTED

-------------------------------------------------------

THEOREM CardinalityUnion ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \cup T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \cup T) =
                              Cardinality(S) + Cardinality(T)
                              - Cardinality(S \cap T)  

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
PROOF
  <1>1. TAKE S, T
  <1>2. ASSUME /\ IsFiniteSet(S)
                 /\ IsFiniteSet(T)
                 /\ Cardinality(T) < Cardinality(S)
        PROVE \A f \in [S -> T] :
                \E x, y \in S : x # y /\ f[x] = f[y]
    <2>1. TAKE f \in [S -> T]
    <2>2. \E x, y \in S : x # y /\ f[x] = f[y]
      <3>1. SUFFICES ASSUME \A x, y \in S : x # y => f[x] # f[y]
                     PROVE  FALSE
        OBVIOUS
      <3>2. DEFINE U == {f[x] : x \in S}
      <3>3. IsBijection(f, S, U)
        BY <2>1, <3>1 DEF IsBijection, U
      <3>4. U \subseteq T
        BY <2>1 DEF U
      <3>5. /\ IsFiniteSet(U)
             /\ Cardinality(U) \leq Cardinality(T)
        BY <1>2, <3>4, FiniteSubset
      <3>6. Cardinality(S) = Cardinality(U)
        BY <1>2, <3>3, <3>5, IsBijectionCardinality
      <3>7. Cardinality(S) \leq Cardinality(T)
        BY <3>5, <3>6
      <3>8. Cardinality(S) \in Nat
        BY <1>2, CardinalityInNat
      <3>9. Cardinality(T) \in Nat
        BY <1>2, CardinalityInNat
      <3>10. FALSE BY <1>2, <3>7, <3>8, <3>9
      <3> QED BY <3>10
    <2> QED BY <2>2
  <1> QED BY <1>2

========================================
