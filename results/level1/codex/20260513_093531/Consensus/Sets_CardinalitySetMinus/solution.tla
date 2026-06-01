-------------------------------- MODULE Sets_CardinalitySetMinus --------------------------------
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
PROOF
<1>1. Cardinality(S) \in Nat BY CardinalityInNat
<1>2. PICK f : IsBijection(f, 1..Cardinality(S), S)
  BY <1>1, CardinalityAxiom
<1>3. PICK k \in 1..Cardinality(S) : f[k] = x
  BY <1>2 DEF IsBijection
<1>. DEFINE g == [i \in 1..(Cardinality(S)-1) |-> IF i < k THEN f[i] ELSE f[i+1]]
<1>4. IsBijection(g, 1..(Cardinality(S)-1), S \ {x})
  <2>1. g \in [1..(Cardinality(S)-1) -> S \ {x}]
    BY <1>1, <1>2, <1>3, SMT DEF IsBijection
  <2>2. \A i, j \in 1..(Cardinality(S)-1) : (i # j) => (g[i] # g[j])
    BY <1>1, <1>2, <1>3, SMT DEF IsBijection
  <2>3. \A y \in S \ {x} : \E i \in 1..(Cardinality(S)-1) : g[i] = y
    <3>1. SUFFICES ASSUME NEW y \in S \ {x}
                   PROVE \E i \in 1..(Cardinality(S)-1) : g[i] = y
      OBVIOUS
    <3>2. PICK j \in 1..Cardinality(S) : f[j] = y
      BY <1>2, <3>1 DEF IsBijection
    <3>3. j # k
      BY <1>2, <1>3, <3>1, <3>2 DEF IsBijection
    <3>4. CASE j < k
      <4>1. j \in 1..(Cardinality(S)-1) /\ g[j] = y
        BY <1>1, <1>3, <3>2, <3>4, SMT
      <4>. QED BY <4>1
    <3>5. CASE j > k
      <4>1. j-1 \in 1..(Cardinality(S)-1) /\ g[j-1] = y
        BY <1>1, <1>3, <3>2, <3>5, SMT
      <4>. QED BY <4>1
    <3>6. j < k \/ j > k
      BY <1>1, <1>3, <3>2, <3>3, SMT
    <3>. QED BY <3>4, <3>5, <3>6
  <2>. QED BY <2>1, <2>2, <2>3 DEF IsBijection
<1>5. IsFiniteSet(S \ {x})
  BY <1>1, <1>4 DEF IsFiniteSet
<1>6. Cardinality(S \ {x}) = Cardinality(S) - 1
  BY <1>1, <1>4, <1>5, CardinalityAxiom
<1>. QED BY <1>5, <1>6

=============================================================================
