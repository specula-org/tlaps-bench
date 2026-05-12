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
<1> DEFINE T == S \ {x}
            n == Cardinality(S)
<1>1. x \notin T
  BY DEF T
<1>2. T \cup {x} = S
  BY DEF T
<1>3. n \in Nat
  BY CardinalityInNat
<1>4. n # 0
  BY <1>2, CardinalityZero
<1>5. n > 0
  BY <1>3, <1>4, SMT
<1>6. \E f : IsBijection(f, 1..n, S)
  BY <1>3, CardinalityAxiom DEF n
<1>7. PICK f : IsBijection(f, 1..n, S)
  BY <1>6
<1>8. \E k \in 1..n : f[k] = x
  BY <1>7 DEF IsBijection
<1>9. PICK k \in 1..n : f[k] = x
  BY <1>8
<1>10. DEFINE p(i) == IF i < k THEN i ELSE i+1
              g == [i \in 1..(n-1) |-> f[p(i)]]
<1>11. IsBijection(g, 1..(n-1), T)
  <2>1. g \in [1..(n-1) -> T]
    <3>1. ASSUME NEW i \in 1..(n-1)
          PROVE  f[p(i)] \in T
      <4>1. CASE i < k
        <5>1. i \in 1..n /\ i # k
          BY <1>3, <1>9, <3>1, <4>1, SMT
        <5>2. f[i] \in S
          BY <1>7, <5>1 DEF IsBijection
        <5>3. f[i] # x
          BY <1>7, <1>9, <5>1 DEF IsBijection
        <5>4. QED
          BY <4>1, <5>2, <5>3 DEF p, T
      <4>2. CASE ~(i < k)
        <5>1. i+1 \in 1..n /\ i+1 # k
          BY <1>3, <1>9, <3>1, <4>2, SMT
        <5>2. f[i+1] \in S
          BY <1>7, <5>1 DEF IsBijection
        <5>3. f[i+1] # x
          BY <1>7, <1>9, <5>1 DEF IsBijection
        <5>4. QED
          BY <4>2, <5>2, <5>3 DEF p, T
      <4>3. QED
        BY <4>1, <4>2
    <3>2. QED
      BY <3>1 DEF g
  <2>2. \A i, j \in 1..(n-1) :
          (i # j) => (g[i] # g[j])
    <3>1. ASSUME NEW i \in 1..(n-1), NEW j \in 1..(n-1), i # j
          PROVE  g[i] # g[j]
      <4>1. p(i) \in 1..n /\ p(j) \in 1..n /\ p(i) # p(j)
        BY <1>3, <1>9, <3>1, SMT DEF p
      <4>2. g[i] = f[p(i)] /\ g[j] = f[p(j)]
        BY <3>1 DEF g
      <4>3. QED
        BY <1>7, <4>1, <4>2 DEF IsBijection
    <3>2. QED
      BY <3>1
  <2>3. \A y \in T : \E i \in 1..(n-1) : g[i] = y
    <3>1. ASSUME NEW y \in T
          PROVE  \E i \in 1..(n-1) : g[i] = y
      <4>1. y \in S /\ y # x
        BY <3>1 DEF T
      <4>2. \E r \in 1..n : f[r] = y
        BY <1>7, <4>1 DEF IsBijection
      <4>3. PICK r \in 1..n : f[r] = y
        BY <4>2
      <4>4. r # k
        BY <1>9, <4>1, <4>3
      <4>5. DEFINE i == IF r < k THEN r ELSE r-1
      <4>6. i \in 1..(n-1)
        BY <1>3, <1>9, <4>3, <4>4, SMT DEF i
      <4>7. p(i) = r
        BY <1>9, <4>3, <4>4, <4>6, SMT DEF i, p
      <4>8. g[i] = y
        BY <4>3, <4>6, <4>7 DEF g
      <4>9. QED
        BY <4>6, <4>8
    <3>2. QED
      BY <3>1
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF IsBijection
<1>12. IsFiniteSet(T)
  BY <1>11, <1>3 DEF IsFiniteSet
<1>13. Cardinality(T) = n - 1
  BY <1>3, <1>11, <1>12, CardinalityAxiom
<1>14. QED
  BY <1>12, <1>13 DEF T, n

=============================================================================
