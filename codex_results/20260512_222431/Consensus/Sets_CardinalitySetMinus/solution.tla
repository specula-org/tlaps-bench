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
  <1>2. \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>1, CardinalityAxiom
  <1>3. PICK f : IsBijection(f, 1..Cardinality(S), S) BY <1>2
  <1>4. \E k \in 1..Cardinality(S) : f[k] = x BY <1>3 DEF IsBijection
  <1>5. PICK k \in 1..Cardinality(S) : f[k] = x BY <1>4
  <1>6. Cardinality(S) # 0 BY <1>5
  <1>. DEFINE n == Cardinality(S)
              g == [i \in 1..(n-1) |-> IF i < k THEN f[i] ELSE f[i+1]]
  <1>7. n \in Nat BY <1>1 DEF n
  <1>7a. n # 0 BY <1>6 DEF n
  <1>7b. n-1 \in Nat BY <1>7, <1>7a, SMT
  <1>8. f \in [1..n -> S] BY <1>3 DEF IsBijection, n
  <1>9. \A a, b \in 1..n : (a # b) => (f[a] # f[b])
    BY <1>3 DEF IsBijection, n
  <1>10. \A y \in S : \E a \in 1..n : f[a] = y
    BY <1>3 DEF IsBijection, n
  <1>11. k \in 1..n /\ f[k] = x BY <1>5 DEF n
  <1>12. g \in [1..(n-1) -> S \ {x}]
  PROOF
    <2>1. SUFFICES ASSUME NEW i \in 1..(n-1)
                      PROVE g[i] \in S \ {x}
      BY DEF g
    <2>2. CASE i < k
      <3>1. i \in 1..n BY <1>7, <2>1, SMT
      <3>2. i # k BY <2>2
      <3>3. f[i] \in S BY <1>8, <3>1
      <3>4. f[i] # x BY <1>9, <1>11, <3>1, <3>2
      <3> QED BY <2>2, <3>3, <3>4 DEF g
    <2>3. CASE ~(i < k)
      <3>1. i+1 \in 1..n BY <1>7, <2>1, SMT
      <3>2. i+1 # k BY <1>11, <2>1, <2>3, SMT
      <3>3. f[i+1] \in S BY <1>8, <3>1
      <3>4. f[i+1] # x BY <1>9, <1>11, <3>1, <3>2
      <3> QED BY <2>3, <3>3, <3>4 DEF g
    <2> QED BY <2>2, <2>3
  <1>13. \A i, j \in 1..(n-1) : (i # j) => (g[i] # g[j])
  PROOF
    <2>1. SUFFICES ASSUME NEW i \in 1..(n-1), NEW j \in 1..(n-1), i # j
                      PROVE g[i] # g[j]
      OBVIOUS
    <2>. DEFINE p(m) == IF m < k THEN m ELSE m+1
    <2>2. p(i) \in 1..n BY <1>7, <1>11, <2>1, SMT DEF p
    <2>3. p(j) \in 1..n BY <1>7, <1>11, <2>1, SMT DEF p
    <2>4. p(i) # p(j) BY <2>1, SMT DEF p
    <2>5. g[i] = f[p(i)] BY <2>1 DEF g, p
    <2>6. g[j] = f[p(j)] BY <2>1 DEF g, p
    <2> QED BY <1>9, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>14. \A y \in S \ {x} : \E i \in 1..(n-1) : g[i] = y
  PROOF
    <2>1. SUFFICES ASSUME NEW y \in S \ {x}
                      PROVE \E i \in 1..(n-1) : g[i] = y
      OBVIOUS
    <2>2. y \in S /\ y # x BY <2>1
    <2>3. PICK j \in 1..n : f[j] = y BY <1>10, <2>2
    <2>4. j # k BY <1>11, <2>2, <2>3
    <2>5. CASE j < k
      <3>1. j \in 1..(n-1) BY <1>7, <1>11, <2>3, <2>5, SMT
      <3>2. g[j] = f[j] BY <3>1, <2>5 DEF g
      <3>3. g[j] = y BY <2>3, <3>2
      <3> QED BY <3>1, <3>3
    <2>6. CASE ~(j < k)
      <3>1. k < j BY <2>4, <2>6
      <3>2. j-1 \in 1..(n-1) BY <1>7, <2>3, <3>1, SMT
      <3>3. (j-1)+1 = j BY SMT
      <3>4. ~((j-1) < k) BY <3>1, SMT
      <3>5. g[j-1] = f[(j-1)+1] BY <3>2, <3>4 DEF g
      <3>6. g[j-1] = y BY <2>3, <3>3, <3>5
      <3> QED BY <3>2, <3>6
    <2> QED BY <2>5, <2>6
  <1>15. IsBijection(g, 1..(n-1), S \ {x})
    BY <1>12, <1>13, <1>14 DEF IsBijection
  <1>16. IsFiniteSet(S \ {x}) BY <1>7, <1>15 DEF IsFiniteSet
  <1>17. Cardinality(S \ {x}) = Cardinality(S) - 1
    BY <1>7b, <1>15, <1>16, CardinalityAxiom DEF n
  <1> QED BY <1>16, <1>17

=============================================================================
