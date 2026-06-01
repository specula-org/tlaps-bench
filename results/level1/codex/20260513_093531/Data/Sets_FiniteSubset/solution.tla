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
  <1>1. DEFINE P(n) == \A U : /\ IsFiniteSet(U)
                                  /\ Cardinality(U) = n
                               => \A V : V \subseteq U =>
                                    /\ IsFiniteSet(V)
                                    /\ Cardinality(V) \leq Cardinality(U)
  <1>2. P(0)
    PROOF
      <2>1. SUFFICES ASSUME NEW U,
                              IsFiniteSet(U),
                              Cardinality(U) = 0
                       PROVE  \A V : V \subseteq U =>
                                /\ IsFiniteSet(V)
                                /\ Cardinality(V) \leq Cardinality(U)
        OBVIOUS
      <2>2. \A V : V \subseteq U =>
              /\ IsFiniteSet(V)
              /\ Cardinality(V) \leq Cardinality(U)
        PROOF
          <3>1. U = {}
            BY <2>1, CardinalityZero
          <3>2. SUFFICES ASSUME NEW V, V \subseteq U
                         PROVE  /\ IsFiniteSet(V)
                                /\ Cardinality(V) \leq Cardinality(U)
            OBVIOUS
          <3>3. /\ IsFiniteSet(V)
                 /\ Cardinality(V) \leq Cardinality(U)
            PROOF
              <4>1. V = {}
                BY <3>1, <3>2
              <4>2. IsFiniteSet(V) /\ Cardinality(V) = 0
                BY <4>1, CardinalityZero
              <4> QED
                BY <2>1, <4>2
          <3> QED
            BY <3>2, <3>3
      <2> QED
        BY <2>2
  <1>3. \A n \in Nat : P(n) => P(n+1)
    PROOF
      <2>1. SUFFICES ASSUME NEW n \in Nat, P(n)
                       PROVE P(n+1)
        OBVIOUS
      <2>2. P(n+1)
        PROOF
          <3>1. SUFFICES ASSUME NEW U,
                                  IsFiniteSet(U),
                                  Cardinality(U) = n+1
                           PROVE \A V : V \subseteq U =>
                                   /\ IsFiniteSet(V)
                                   /\ Cardinality(V) \leq Cardinality(U)
            OBVIOUS
          <3>2. \A V : V \subseteq U =>
                  /\ IsFiniteSet(V)
                  /\ Cardinality(V) \leq Cardinality(U)
            PROOF
              <4>1. SUFFICES ASSUME NEW V, V \subseteq U
                             PROVE  /\ IsFiniteSet(V)
                                    /\ Cardinality(V) \leq Cardinality(U)
                OBVIOUS
              <4>2. /\ IsFiniteSet(V)
                     /\ Cardinality(V) \leq Cardinality(U)
                PROOF
                  <5>1. CASE V = U
                    BY <3>1, <5>1
                  <5>2. CASE V # U
                    PROOF
                      <6>1. \E x : x \in U /\ x \notin V
                        BY <4>1, <5>2
                      <6>2. PICK x : x \in U /\ x \notin V
                        BY <6>1
                      <6>3. /\ IsFiniteSet(U \ {x})
                             /\ Cardinality(U \ {x}) = Cardinality(U) - 1
                        BY <3>1, <6>2, CardinalitySetMinus
                      <6>4. Cardinality(U \ {x}) = n
                        BY <2>1, <3>1, <6>3
                      <6>5. V \subseteq U \ {x}
                        BY <4>1, <6>2
                      <6>6. /\ IsFiniteSet(V)
                             /\ Cardinality(V) \leq Cardinality(U \ {x})
                        BY <2>1, <6>3, <6>4, <6>5 DEF P
                      <6>7. Cardinality(V) \leq n
                        BY <6>4, <6>6
                      <6>8. Cardinality(V) \in Nat
                        BY <6>6, CardinalityInNat
                      <6>9. n \leq n+1
                        BY <2>1, Z3
                      <6>10. Cardinality(V) \leq n+1
                        BY <2>1, <6>7, <6>8, <6>9, Isa
                      <6>11. Cardinality(V) \leq Cardinality(U)
                        BY <3>1, <6>10
                      <6> QED
                        BY <6>6, <6>11
                  <5> QED
                    BY <5>1, <5>2
              <4> QED
                BY <4>1, <4>2
          <3> QED
            BY <3>2
      <2> QED
        BY <2>2
  <1>4. HIDE DEF P
  <1>5. \A n \in Nat : P(n)
    BY <1>2, <1>3, NatInduction, Isa
  <1>6. Cardinality(TT) \in Nat
    BY CardinalityInNat
  <1>7. P(Cardinality(TT))
    BY <1>5, <1>6
  <1> QED
    BY <1>7 DEF P

=============================================================================
