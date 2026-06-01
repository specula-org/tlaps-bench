---- MODULE PaxosProof_FiniteSubset ----
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
  <1> DEFINE P(n) == \A T : IsFiniteSet(T) /\ Cardinality(T) = n =>
                       \A U \in SUBSET T : /\ IsFiniteSet(U)
                                          /\ Cardinality(U) \leq Cardinality(T)
  <1>1. P(0)
    <2>1. SUFFICES ASSUME NEW T,
                         IsFiniteSet(T) /\ Cardinality(T) = 0,
                         NEW U \in SUBSET T
                  PROVE  /\ IsFiniteSet(U)
                         /\ Cardinality(U) \leq Cardinality(T)
      BY DEF P
    <2>2. T = {}
      BY <2>1, CardinalityZero
    <2>3. U = {}
      BY <2>1, <2>2
    <2>4. IsFiniteSet(U) /\ Cardinality(U) = 0
      BY <2>3, CardinalityZero
    <2>5. QED
      BY <2>1, <2>4
  <1>2. \A n \in Nat : P(n) => P(n+1)
    <2>1. SUFFICES ASSUME NEW n \in Nat, P(n)
                  PROVE  P(n+1)
      OBVIOUS
    <2>2. SUFFICES ASSUME NEW T,
                         IsFiniteSet(T) /\ Cardinality(T) = n+1,
                         NEW U \in SUBSET T
                  PROVE  /\ IsFiniteSet(U)
                         /\ Cardinality(U) \leq Cardinality(T)
      BY <2>1 DEF P
    <2>3. CASE U = T
      <3>1. IsFiniteSet(U)
        BY <2>2, <2>3
      <3>2. Cardinality(U) = Cardinality(T)
        BY <2>3
      <3>3. Cardinality(U) \in Nat
        BY <3>1, CardinalityInNat
      <3>4. Cardinality(U) \leq Cardinality(T)
        BY <3>2, <3>3, SMT
      <3>5. QED
        BY <3>1, <3>4
    <2>4. CASE U # T
      <3>1. PICK x \in T : x \notin U
        BY <2>2, <2>4
      <3>2. LET T0 == T \ {x} IN
              /\ IsFiniteSet(T0)
              /\ Cardinality(T0) = n
        BY <2>1, <2>2, <3>1, CardinalitySetMinus, SMT
      <3>3. U \in SUBSET (T \ {x})
        BY <2>2, <3>1
      <3>4. /\ IsFiniteSet(U)
             /\ Cardinality(U) \leq Cardinality(T \ {x})
        BY <2>1, <3>2, <3>3 DEF P
      <3>5. Cardinality(T \ {x}) = n
        BY <3>2
      <3>6. Cardinality(T) = n + 1
        BY <2>2
      <3>7. Cardinality(T \ {x}) \leq Cardinality(T)
        BY <3>5, <3>6, SMT
      <3>8. Cardinality(U) \leq Cardinality(T \ {x})
        BY <3>4
      <3>9. Cardinality(U) \in Nat
        BY <3>4, CardinalityInNat
      <3>10. Cardinality(T \ {x}) \in Nat
        BY <3>2, CardinalityInNat
      <3>11. Cardinality(T) \in Nat
        BY <2>2, CardinalityInNat
      <3>12. Cardinality(U) \leq Cardinality(T)
        BY <3>7, <3>8, <3>9, <3>10, <3>11, SMT
      <3>13. QED
        BY <3>4, <3>12
    <2>5. QED
      BY <2>3, <2>4
  <1>3. \A n \in Nat : P(n)
    BY <1>1, <1>2, NatInduction
  <1>4. Cardinality(TT) \in Nat
    BY CardinalityInNat
  <1>5. S \in SUBSET TT
    BY SMT
  <1>6. QED
    BY <1>3, <1>4, <1>5

========================================
