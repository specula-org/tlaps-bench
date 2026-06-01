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
  <1>1. Cardinality(S) \in Nat
    BY CardinalityInNat
  <1>2. \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>1, CardinalityAxiom DEF IsFiniteSet
  <1>3. PICK f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>2
  <1>4. \E i \in 1..Cardinality(S) : f[i] = x
    BY <1>3 DEF IsBijection
  <1>5. PICK i \in 1..Cardinality(S) : f[i] = x
    BY <1>4
  <1>6. DEFINE g[j \in 1..(Cardinality(S)-1)] ==
            IF j < i THEN f[j] ELSE f[j+1]
  <1>7. IsBijection(g, 1..(Cardinality(S)-1), S \ {x})
    <2>1. g \in [1..(Cardinality(S)-1) -> S \ {x}]
        <3>1. SUFFICES ASSUME NEW j \in 1..(Cardinality(S)-1)
              PROVE  g[j] \in S \ {x}
        BY DEF g
      <3>2. CASE j < i
        <4>1. j \in 1..Cardinality(S) BY SMT, <1>1, <1>5, <3>1, <3>2
        <4>2. j # i BY Isa, <3>2
        <4>3. f[j] \in S BY <1>3, <4>1 DEF IsBijection
        <4>4. f[j] # x BY <1>3, <1>5, <4>1, <4>2 DEF IsBijection
        <4>5. g[j] = f[j] BY <3>1, <3>2 DEF g
        <4>. QED BY <4>3, <4>4, <4>5
      <3>3. CASE ~(j < i)
        <4>1. j+1 \in 1..Cardinality(S) BY SMT, <1>1, <1>5, <3>1, <3>3
        <4>2. j+1 # i BY SMT, <3>3
        <4>3. f[j+1] \in S BY <1>3, <4>1 DEF IsBijection
        <4>4. f[j+1] # x BY <1>3, <1>5, <4>1, <4>2 DEF IsBijection
        <4>5. g[j] = f[j+1] BY <3>1, <3>3 DEF g
        <4>. QED BY <4>3, <4>4, <4>5
      <3>. QED BY <3>2, <3>3
    <2>2. \A j, k \in 1..(Cardinality(S)-1) : (j # k) => (g[j] # g[k])
        <3>1. SUFFICES ASSUME NEW j \in 1..(Cardinality(S)-1),
                            NEW k \in 1..(Cardinality(S)-1),
                            j # k
              PROVE  g[j] # g[k]
        OBVIOUS
      <3>2. CASE j < i /\ k < i
        <4>1. j \in 1..Cardinality(S) /\ k \in 1..Cardinality(S)
          BY SMT, <1>1, <3>1, <3>2
        <4>2. g[j] = f[j] /\ g[k] = f[k] BY <3>1, <3>2 DEF g
        <4>. QED BY <1>3, <3>1, <4>1, <4>2 DEF IsBijection
      <3>3. CASE j < i /\ ~(k < i)
        <4>1. j \in 1..Cardinality(S) /\ k+1 \in 1..Cardinality(S)
          BY SMT, <1>1, <1>5, <3>1, <3>3
        <4>2. j # k+1 BY SMT, <3>1, <3>3
        <4>3. g[j] = f[j] /\ g[k] = f[k+1] BY <3>1, <3>3 DEF g
        <4>. QED BY <1>3, <4>1, <4>2, <4>3 DEF IsBijection
      <3>4. CASE ~(j < i) /\ k < i
        <4>1. j+1 \in 1..Cardinality(S) /\ k \in 1..Cardinality(S)
          BY SMT, <1>1, <1>5, <3>1, <3>4
        <4>2. j+1 # k BY SMT, <3>1, <3>4
        <4>3. g[j] = f[j+1] /\ g[k] = f[k] BY <3>1, <3>4 DEF g
        <4>. QED BY <1>3, <4>1, <4>2, <4>3 DEF IsBijection
      <3>5. CASE ~(j < i) /\ ~(k < i)
        <4>1. j+1 \in 1..Cardinality(S) /\ k+1 \in 1..Cardinality(S)
          BY SMT, <1>1, <3>1, <3>5
        <4>2. j+1 # k+1 BY SMT, <3>1
        <4>3. g[j] = f[j+1] /\ g[k] = f[k+1] BY <3>1, <3>5 DEF g
        <4>. QED BY <1>3, <4>1, <4>2, <4>3 DEF IsBijection
      <3>. QED BY <3>2, <3>3, <3>4, <3>5
    <2>3. \A y \in S \ {x} : \E j \in 1..(Cardinality(S)-1) : g[j] = y
        <3>1. SUFFICES ASSUME NEW y \in S \ {x}
              PROVE  \E j \in 1..(Cardinality(S)-1) : g[j] = y
        OBVIOUS
      <3>2. \E k \in 1..Cardinality(S) : f[k] = y
        BY <1>3, <3>1 DEF IsBijection
      <3>3. PICK k \in 1..Cardinality(S) : f[k] = y
        BY <3>2
      <3>4. k # i
        BY <1>5, <3>1, <3>3
      <3>5. CASE k < i
        <4>1. k \in 1..(Cardinality(S)-1) BY SMT, <1>1, <1>5, <3>3, <3>5
        <4>2. g[k] = f[k] BY <3>5, <4>1 DEF g
        <4>. QED BY <3>3, <4>1, <4>2
      <3>6. CASE ~(k < i)
        <4>1. k-1 \in 1..(Cardinality(S)-1) BY SMT, <1>1, <1>5, <3>3, <3>4, <3>6
        <4>2. ~(k-1 < i) BY SMT, <3>4, <3>6
        <4>3. g[k-1] = f[k] BY <4>1, <4>2 DEF g
        <4>. QED BY <3>3, <4>1, <4>3
      <3>. QED BY <3>5, <3>6
    <2>. QED BY <2>1, <2>2, <2>3 DEF IsBijection
  <1>8. IsFiniteSet(S \ {x})
    BY <1>1, <1>7 DEF IsFiniteSet
  <1>9. Cardinality(S \ {x}) = Cardinality(S) - 1
    BY <1>1, <1>7, <1>8, CardinalityAxiom
  <1>. QED BY <1>8, <1>9

=============================================================================
