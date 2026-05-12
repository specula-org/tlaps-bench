---- MODULE Consensus_FiniteSubset ----
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
<1>. DEFINE P(n) == \A T : /\ IsFiniteSet(T)
                           /\ Cardinality(T) = n
                           => \A U : U \subseteq T
                                     => /\ IsFiniteSet(U)
                                        /\ Cardinality(U) \leq Cardinality(T)
<1>1. P(0)
  <2>1. ASSUME NEW T,
               /\ IsFiniteSet(T)
               /\ Cardinality(T) = 0
        PROVE  \A U : U \subseteq T
                  => /\ IsFiniteSet(U)
                     /\ Cardinality(U) \leq Cardinality(T)
    <3>1. T = {}
      BY <2>1, CardinalityZero
    <3>2. ASSUME NEW U, U \subseteq T
          PROVE  /\ IsFiniteSet(U)
                 /\ Cardinality(U) \leq Cardinality(T)
      <4>1. U = {}
        BY <3>1, <3>2
      <4>2. /\ IsFiniteSet(U)
             /\ Cardinality(U) = 0
        BY <4>1, CardinalityZero
      <4>. QED
        BY <2>1, <4>2
    <3>. QED
      BY <3>2
  <2>. QED
    BY <2>1 DEF P
<1>2. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n + 1)
  <2>1. ASSUME NEW T,
               /\ IsFiniteSet(T)
               /\ Cardinality(T) = n + 1
        PROVE  \A U : U \subseteq T
                  => /\ IsFiniteSet(U)
                     /\ Cardinality(U) \leq Cardinality(T)
    <3>1. ASSUME NEW U, U \subseteq T
          PROVE  /\ IsFiniteSet(U)
                 /\ Cardinality(U) \leq Cardinality(T)
      <4>1. CASE U = T
        <5>1. IsFiniteSet(U)
          BY <2>1, <4>1
        <5>2. Cardinality(U) = Cardinality(T)
          BY <4>1
        <5>3. Cardinality(T) \in Nat
          BY <2>1, CardinalityInNat
        <5>4. Cardinality(U) \leq Cardinality(T)
          BY <5>2, <5>3, SMT
        <5>. QED
          BY <5>1, <5>4
      <4>2. CASE U # T
        <5>1. \E x : x \in T /\ x \notin U
          BY <3>1, <4>2
        <5>2. PICK x : x \in T /\ x \notin U
          BY <5>1
        <5>3. /\ IsFiniteSet(T \ {x})
               /\ Cardinality(T \ {x}) = Cardinality(T) - 1
          BY <2>1, <5>2, CardinalitySetMinus
        <5>4. Cardinality(T \ {x}) = n
          BY <2>1, <5>3
        <5>5. U \subseteq T \ {x}
          BY <3>1, <5>2
        <5>6. /\ IsFiniteSet(U)
               /\ Cardinality(U) \leq Cardinality(T \ {x})
          BY <1>2, <5>3, <5>4, <5>5 DEF P
        <5>7. Cardinality(T \ {x}) \leq Cardinality(T)
          BY <1>2, <2>1, <5>3, <5>4, SMT
        <5>8. Cardinality(U) \in Nat
          BY <5>6, CardinalityInNat
        <5>9. Cardinality(T \ {x}) \in Nat
          BY <5>3, CardinalityInNat
        <5>10. Cardinality(T) \in Nat
          BY <2>1, CardinalityInNat
        <5>11. Cardinality(U) \leq Cardinality(T)
          BY <5>6, <5>7, <5>8, <5>9, <5>10, SMT
        <5>. QED
          BY <5>6, <5>11
      <4>. QED
        BY <4>1, <4>2
    <3>. QED
      BY <3>1
  <2>. QED
    BY <2>1 DEF P
<1>. HIDE DEF P
<1>3. \A n \in Nat : P(n)
  BY <1>1, <1>2, NatInduction, IsaM("blast")
<1>4. Cardinality(TT) \in Nat
  BY CardinalityInNat
<1>5. P(Cardinality(TT))
  BY <1>3, <1>4
<1>. QED
  BY <1>5 DEF P

========================================
