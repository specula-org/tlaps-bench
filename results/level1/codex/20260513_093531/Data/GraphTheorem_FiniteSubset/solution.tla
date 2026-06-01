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
<1>1. DEFINE P(n) == \A T : IsFiniteSet(T) /\ Cardinality(T) = n =>
                            \A U : U \subseteq T =>
                              /\ IsFiniteSet(U)
                              /\ Cardinality(U) \leq Cardinality(T)
<1>2. P(0)
  <2>1. ASSUME NEW T,
                IsFiniteSet(T) /\ Cardinality(T) = 0,
                NEW U,
                U \subseteq T
          PROVE /\ IsFiniteSet(U)
                /\ Cardinality(U) \leq Cardinality(T)
    <3>1. T = {}
      BY <2>1, CardinalityZero
    <3>2. U = {}
      BY <2>1, <3>1
    <3>3. /\ IsFiniteSet(U)
          /\ Cardinality(U) = 0
      BY <3>2, CardinalityZero
    <3>. QED
      BY <2>1, <3>3, Z3
  <2>. QED
    BY <2>1 DEF P
<1>3. ASSUME NEW n \in Nat, P(n)
      PROVE P(n+1)
  <2>1. ASSUME NEW T,
                IsFiniteSet(T) /\ Cardinality(T) = n+1,
                NEW U,
                U \subseteq T
          PROVE /\ IsFiniteSet(U)
                /\ Cardinality(U) \leq Cardinality(T)
    <3>1. PICK x \in T : TRUE
      BY <2>1, CardinalityZero, Z3
    <3>2. /\ IsFiniteSet(T \ {x})
          /\ Cardinality(T \ {x}) = n
      BY <2>1, <3>1, CardinalitySetMinus, Z3
    <3>3. CASE x \in U
      <4>1. U \ {x} \subseteq T \ {x}
        BY <2>1, <3>3
      <4>2. /\ IsFiniteSet(U \ {x})
            /\ Cardinality(U \ {x}) \leq Cardinality(T \ {x})
        BY <1>3, <3>2, <4>1 DEF P
      <4>3. x \notin (U \ {x})
        BY <3>3
      <4>4. /\ IsFiniteSet((U \ {x}) \cup {x})
            /\ Cardinality((U \ {x}) \cup {x}) = Cardinality(U \ {x}) + 1
        BY <4>2, <4>3, CardinalityPlusOne
      <4>5. (U \ {x}) \cup {x} = U
        BY <3>3
      <4>6. Cardinality(U \ {x}) \in Nat
        BY <4>2, CardinalityInNat
      <4>. QED
        BY <2>1, <3>2, <4>2, <4>4, <4>5, <4>6, Isa
    <3>4. CASE x \notin U
      <4>1. U \subseteq T \ {x}
        BY <2>1, <3>4
      <4>2. /\ IsFiniteSet(U)
            /\ Cardinality(U) \leq Cardinality(T \ {x})
        BY <1>3, <3>2, <4>1 DEF P
      <4>3. Cardinality(U) \in Nat
        BY <4>2, CardinalityInNat
      <4>. QED
        BY <2>1, <3>2, <4>2, <4>3, Isa
    <3>. QED
      BY <3>3, <3>4
  <2>. QED
    BY <2>1 DEF P
<1>. HIDE DEF P
<1>4. \A n \in Nat : P(n)
  BY <1>2, <1>3, NatInduction, Isa
<1>5. Cardinality(TT) \in Nat
  BY CardinalityInNat
<1>. QED
  BY <1>4, <1>5 DEF P

========================================
