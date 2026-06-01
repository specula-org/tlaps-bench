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
PROOF
<1>. DEFINE P(n) == \A T : /\ IsFiniteSet(T)
                            /\ Cardinality(T) = n
                            => \A A : A \subseteq T
                                      => /\ IsFiniteSet(A)
                                         /\ Cardinality(A) \leq Cardinality(T)
<1>1. P(0)
  <2>. SUFFICES ASSUME NEW T, /\ IsFiniteSet(T)
                              /\ Cardinality(T) = 0,
                       NEW A, A \subseteq T
                PROVE  /\ IsFiniteSet(A)
                       /\ Cardinality(A) \leq Cardinality(T)
    BY DEF P
  <2>1. T = {} BY CardinalityZero
  <2>2. A = {} BY <2>1, Zenon
  <2>3. /\ IsFiniteSet({})
        /\ Cardinality({}) = 0
    BY CardinalityZero
  <2>4. IsFiniteSet(A)
    BY <2>2, <2>3
  <2>5. Cardinality(A) \leq Cardinality(T)
    BY <2>2, <2>3, SMT
  <2>. QED BY <2>4, <2>5
<1>2. \A n \in Nat : P(n) => P(n+1)
  <2>. SUFFICES ASSUME NEW n \in Nat, P(n)
                PROVE  P(n+1)
    OBVIOUS
  <2>. SUFFICES ASSUME NEW T, /\ IsFiniteSet(T)
                              /\ Cardinality(T) = n+1,
                       NEW A, A \subseteq T
                PROVE  /\ IsFiniteSet(A)
                       /\ Cardinality(A) \leq Cardinality(T)
    BY DEF P
  <2>1. T # {}
    BY CardinalityZero, SMT
  <2>2. PICK x : x \in T BY <2>1, Zenon
  <2>. DEFINE T0 == T \ {x}
              A0 == A \ {x}
  <2>3. /\ IsFiniteSet(T0)
        /\ Cardinality(T0) = Cardinality(T) - 1
    BY <2>2, CardinalitySetMinus DEF T0
  <2>4. Cardinality(T0) = n
    BY <2>3, SMT
  <2>4a. Cardinality(T) = Cardinality(T0) + 1
    BY <2>3, SMT
  <2>5. CASE x \in A
    <3>1. A0 \subseteq T0
      BY DEF A0, T0
    <3>2. /\ IsFiniteSet(A0)
          /\ Cardinality(A0) \leq Cardinality(T0)
      BY <2>3, <2>4, <3>1 DEF P
    <3>3. x \notin A0
      BY DEF A0
    <3>4. /\ IsFiniteSet(A0 \cup {x})
          /\ Cardinality(A0 \cup {x}) = Cardinality(A0) + 1
      BY <3>2, <3>3, CardinalityPlusOne
    <3>5. A = A0 \cup {x}
      BY <2>5 DEF A0
    <3>6. IsFiniteSet(A)
      BY <3>4, <3>5
    <3>7. Cardinality(A) = Cardinality(A0) + 1
      BY <3>4, <3>5
    <3>7a. Cardinality(A0) \in Nat
      BY <3>2, CardinalityInNat
    <3>8. Cardinality(A) \leq Cardinality(T)
      BY <2>4, <2>4a, <3>2, <3>7, <3>7a, SMT
    <3>. QED BY <3>6, <3>8
  <2>6. CASE x \notin A
    <3>1. A \subseteq T0
      BY <2>2, <2>6 DEF T0
    <3>2. /\ IsFiniteSet(A)
          /\ Cardinality(A) \leq Cardinality(T0)
      BY <2>3, <2>4, <3>1 DEF P
    <3>2a. Cardinality(T0) \in Nat
      BY <2>3, CardinalityInNat
    <3>2b. Cardinality(A) \in Nat
      BY <3>2, CardinalityInNat
    <3>3. Cardinality(A) \leq n
      BY <2>4, <3>2, <3>2b, SMT
    <3>4. Cardinality(A) \leq Cardinality(T)
      BY <3>3, <3>2b, SMT
    <3>. QED BY <3>2, <3>4
  <2>. QED BY <2>5, <2>6
<1>3. \A n \in Nat : P(n)
  <2>. HIDE DEF P
  <2>. QED BY <1>1, <1>2, NatInduction
<1>4. Cardinality(TT) \in Nat
  BY CardinalityInNat
<1>5. P(Cardinality(TT))
  BY <1>3, <1>4
<1>. QED BY <1>5 DEF P

========================================
