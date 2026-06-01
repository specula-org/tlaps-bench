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
<1>. DEFINE P(n) ==
        \A T : IsFiniteSet(T) /\ Cardinality(T) = n =>
          \A U : U \subseteq T =>
            /\ IsFiniteSet(U)
            /\ Cardinality(U) \leq Cardinality(T)
<1>1. P(0)
  <2>0. SUFFICES ASSUME NEW T, IsFiniteSet(T), Cardinality(T) = 0,
                       NEW U, U \subseteq T
                PROVE  /\ IsFiniteSet(U)
                       /\ Cardinality(U) \leq Cardinality(T)
    OBVIOUS
  <2>1. T = {}  BY <2>0, CardinalityZero
  <2>2. U = {}  BY <2>0, <2>1
  <2>3. /\ IsFiniteSet({})
        /\ Cardinality({}) = 0
    BY CardinalityZero
  <2>. QED BY <2>0, <2>1, <2>2, <2>3
<1>2. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n+1)
  <2>0. SUFFICES ASSUME NEW T, IsFiniteSet(T), Cardinality(T) = n+1,
                       NEW U, U \subseteq T
                PROVE  /\ IsFiniteSet(U)
                       /\ Cardinality(U) \leq Cardinality(T)
    OBVIOUS
  <2>1. CASE U = T
    BY <2>1, <2>0, CardinalityInNat
  <2>2. CASE U # T
    <3>1. PICK x \in T \ U : TRUE
      BY <2>2, <2>0
    <3>2. /\ IsFiniteSet(T \ {x})
          /\ Cardinality(T \ {x}) = Cardinality(T) - 1
      BY <3>1, <2>0, CardinalitySetMinus
    <3>3. Cardinality(T \ {x}) = n
      BY <3>2, <2>0
    <3>4. U \subseteq T \ {x}
      BY <3>1, <2>0
    <3>5. /\ IsFiniteSet(U)
          /\ Cardinality(U) \leq Cardinality(T \ {x})
      BY <1>2, <3>2, <3>3, <3>4 DEF P
    <3>6. Cardinality(U) \leq n
      BY <3>3, <3>5
    <3>7. n \leq n+1
      BY <1>2, Isa
    <3>8. Cardinality(T) = n+1
      BY <2>0
    <3>8a. Cardinality(U) \in Int
      BY <3>5, CardinalityInNat, Isa
    <3>9. Cardinality(U) \leq Cardinality(T)
      BY <3>6, <3>7, <3>8, <3>8a, <1>2, Z3
    <3>10. IsFiniteSet(U)
      BY <3>5
    <3>. QED BY <3>9, <3>10
  <2>. QED BY <2>1, <2>2
<1>3. \A n \in Nat : P(n) => P(n+1)
  BY <1>2
<1>3a. HIDE DEF P
<1>4. \A n \in Nat : P(n)
  BY <1>1, <1>3, NatInduction
<1>5. Cardinality(TT) \in Nat
  BY CardinalityInNat
<1>. QED BY <1>4, <1>5 DEF P

=============================================================================
