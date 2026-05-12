---- MODULE Consensus_CardinalitySetMinus ----
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
PROOF
  <1>1. Cardinality(S) \in Nat BY CardinalityInNat
  <1>2. \E f : IsBijection(f, 1..Cardinality(S), S)
    BY <1>1, CardinalityAxiom
  <1>3. PICK f : IsBijection(f, 1..Cardinality(S), S) BY <1>2
  <1>4. \E k \in 1..Cardinality(S) : f[k] = x BY <1>3 DEF IsBijection
  <1>5. PICK k \in 1..Cardinality(S) : f[k] = x BY <1>4
  <1>6. Cardinality(S) # 0 BY <1>5
  <1>. DEFINE n == Cardinality(S)
              U == 1..(n-1)
              h(i) == IF i < k THEN i ELSE i+1
              g == [i \in U |-> f[h(i)]]
  <1>7. k \in 1..n BY <1>5 DEF n
  <1>8. n \in Nat BY <1>1 DEF n
  <1>9. \A i \in U : h(i) \in 1..n /\ h(i) # k
    PROOF
      <2>1. TAKE i \in U
      <2>2. CASE i < k
        <3>1. h(i) = i BY <2>2 DEF h
        <3>2. i \in 1..n /\ i # k BY <1>7, <1>8, <2>1, <2>2, SMT DEF U
        <3>3. QED BY <3>1, <3>2
      <2>3. CASE ~(i < k)
        <3>1. h(i) = i+1 BY <2>3 DEF h
        <3>2. i+1 \in 1..n /\ i+1 # k BY <1>7, <1>8, <2>1, <2>3, SMT DEF U
        <3>3. QED BY <3>1, <3>2
      <2>4. QED BY <2>2, <2>3
  <1>10. \A i, j \in U : i # j => h(i) # h(j)
    BY <1>7, <1>8, <1>6, SMT DEF U, h
  <1>11. \A j \in 1..n : j # k => \E i \in U : h(i) = j
    PROOF
      <2>1. TAKE j \in 1..n
      <2>2. SUFFICES ASSUME j # k PROVE \E i \in U : h(i) = j OBVIOUS
      <2>3. CASE j < k
        <3>1. j \in U BY <1>7, <1>8, <2>1, <2>3, SMT DEF U
        <3>2. h(j) = j BY <2>3 DEF h
        <3>3. QED BY <3>1, <3>2
      <2>4. CASE ~(j < k)
        <3>1. j-1 \in U BY <1>7, <1>8, <2>1, <2>2, <2>4, SMT DEF U
        <3>2. ~(j-1 < k) BY <2>2, <2>4
        <3>3. h(j-1) = j BY <3>2 DEF h
        <3>4. QED BY <3>1, <3>3
      <2>5. QED BY <2>3, <2>4
  <1>12. f \in [1..n -> S] BY <1>3 DEF IsBijection, n
  <1>13. \A i, j \in 1..n : (i # j) => (f[i] # f[j])
    BY <1>3 DEF IsBijection, n
  <1>14. \A y \in S : \E j \in 1..n : f[j] = y
    BY <1>3 DEF IsBijection, n
  <1>15. f[k] = x BY <1>5
  <1>16. g \in [U -> S \ {x}]
    BY <1>9, <1>12, <1>13, <1>15, SMT DEF g
  <1>17. \A i, j \in U : (i # j) => (g[i] # g[j])
    BY <1>9, <1>10, <1>13 DEF g
  <1>18. \A y \in S \ {x} : \E i \in U : g[i] = y
    BY <1>11, <1>13, <1>14, <1>15 DEF g
  <1>19. IsBijection(g, U, S \ {x})
    BY <1>16, <1>17, <1>18 DEF IsBijection
  <1>20. IsBijection(g, 1..(Cardinality(S)-1), S \ {x})
    BY <1>19 DEF U, n
  <1>21. IsFiniteSet(S \ {x})
    BY <1>1, <1>20 DEF IsFiniteSet
  <1>22. Cardinality(S \ {x}) = Cardinality(S) - 1
    BY <1>1, <1>20, <1>21, CardinalityAxiom
  <1> QED BY <1>21, <1>22

========================================
