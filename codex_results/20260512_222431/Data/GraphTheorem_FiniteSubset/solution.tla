---- MODULE GraphTheorem_FiniteSubset ----
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
PROOF
  <1> DEFINE P(n) == \A U : /\ IsFiniteSet(U)
                              /\ Cardinality(U) = n
                              => \A A : A \subseteq U
                                        => /\ IsFiniteSet(A)
                                           /\ Cardinality(A) \leq Cardinality(U)
  <1>1. P(0)
      <2>1. ASSUME NEW U,
                    /\ IsFiniteSet(U)
                    /\ Cardinality(U) = 0
            PROVE  \A A : A \subseteq U
                          => /\ IsFiniteSet(A)
                             /\ Cardinality(A) \leq Cardinality(U)
          <3>1. U = {}
            BY <2>1, CardinalityZero
          <3>2. ASSUME NEW A, A \subseteq U
                 PROVE  /\ IsFiniteSet(A)
                        /\ Cardinality(A) \leq Cardinality(U)
            <4>1. A = {}
              BY <3>1, <3>2, SetExtensionality
            <4>2. IsFiniteSet(A) /\ Cardinality(A) \leq Cardinality(U)
              BY <2>1, <4>1, CardinalityZero
            <4> QED BY <4>2
          <3> QED BY <3>2
      <2> QED BY <2>1
  <1>2. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
      <2>1. ASSUME NEW n \in Nat,
                    \A m \in 0..(n-1) : P(m)
             PROVE  P(n)
        <3>1. ASSUME NEW U,
                        /\ IsFiniteSet(U)
                        /\ Cardinality(U) = n
                PROVE  \A A : A \subseteq U
                              => /\ IsFiniteSet(A)
                                 /\ Cardinality(A) \leq Cardinality(U)
          <4>1. ASSUME NEW A, A \subseteq U
                     PROVE  /\ IsFiniteSet(A)
                            /\ Cardinality(A) \leq Cardinality(U)
            <5>1. CASE A = U
              BY <3>1, <5>1
            <5>2. CASE A # U
                PROOF
                  <6>1. \E x : x \in U /\ x \notin A
                    BY <4>1, <5>2, SetExtensionality
                  <6>2. PICK x : x \in U /\ x \notin A
                    BY <6>1
                  <6>3. /\ IsFiniteSet(U \ {x})
                        /\ Cardinality(U \ {x}) = Cardinality(U) - 1
                    BY <3>1, <6>2, CardinalitySetMinus
                  <6>4. A \subseteq U \ {x}
                    BY <4>1, <6>2, SetExtensionality
                  <6>5. n # 0
                    BY <3>1, <6>2, CardinalityZero
                  <6>6. n-1 \in 0..(n-1)
                    BY <2>1, <6>5
                  <6>7. P(n-1)
                    BY <2>1, <6>6
                  <6>8. Cardinality(U \ {x}) = n-1
                    BY <3>1, <6>3
                  <6>9. /\ IsFiniteSet(A)
                        /\ Cardinality(A) \leq Cardinality(U \ {x})
                    BY <6>3, <6>4, <6>7, <6>8 DEF P
                  <6>10. Cardinality(U \ {x}) \leq Cardinality(U)
                    BY <2>1, <3>1, <6>3, <6>5, Z3
                  <6>11. IsFiniteSet(A)
                    BY <6>9
                  <6>12. Cardinality(A) \in Nat
                    BY <6>9, CardinalityInNat
                  <6>13. Cardinality(U \ {x}) \in Nat
                    BY <6>3, CardinalityInNat
                  <6>14. Cardinality(U) \in Nat
                    BY <3>1, CardinalityInNat
                  <6>15. Cardinality(A) \leq Cardinality(U \ {x})
                    BY <6>9
                  <6>16. Cardinality(A) \leq Cardinality(U)
                    BY <6>10, <6>12, <6>13, <6>14, <6>15, Z3
                  <6>17. /\ IsFiniteSet(A)
                         /\ Cardinality(A) \leq Cardinality(U)
                    BY <6>11, <6>16
                  <6> QED BY <6>17
            <5>3. QED
              BY <5>1, <5>2
          <4> QED BY <4>1
        <3> QED BY <3>1
      <2> QED BY <2>1
  <1> DEFINE Q(n) == \A m \in 0..n : P(m)
  <1>3. Q(0)
    <2>1. ASSUME NEW m \in 0..0
           PROVE  P(m)
      <3>1. m = 0
        BY <2>1, SMT
      <3>2. P(m)
        BY <1>1, <3>1
      <3> QED BY <3>2
    <2> QED BY <2>1 DEF Q
  <1>4. \A n \in Nat : Q(n) => Q(n+1)
    <2>1. ASSUME NEW n \in Nat, Q(n)
           PROVE  Q(n+1)
      <3>1. ASSUME NEW m \in 0..(n+1)
             PROVE  P(m)
        <4>1. m \in 0..n \/ m = n+1
          BY <2>1, <3>1, SMT
        <4>2. CASE m \in 0..n
          BY <2>1, <4>2 DEF Q
        <4>3. CASE m = n+1
          <5>1. \A k \in 0..n : P(k)
            BY <2>1 DEF Q
          <5>2. P(n+1)
            BY <1>2, <2>1, <5>1 DEF Q
          <5>3. P(m)
            BY <4>3, <5>2
          <5> QED BY <5>3
        <4>4. QED
          BY <4>1, <4>2, <4>3
      <3> QED BY <3>1 DEF Q
    <2> QED BY <2>1
  <1>5. \A n \in Nat : Q(n)
    BY <1>3, <1>4, NatInduction, Isa
  <1>6. \A n \in Nat : P(n)
    <2>1. ASSUME NEW n \in Nat
           PROVE  P(n)
      <3>1. Q(n)
        BY <1>5, <2>1
      <3>2. n \in 0..n
        BY <2>1, SMT
      <3>3. P(n)
        BY <3>1, <3>2 DEF Q
      <3> QED BY <3>3
    <2> QED BY <2>1
  <1>7. Cardinality(TT) \in Nat
    BY CardinalityInNat
  <1>8. P(Cardinality(TT))
    BY <1>6, <1>7
  <1>9. QED
    BY <1>8

========================================
