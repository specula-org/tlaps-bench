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

  
------------------------------------------------------------------



------------------------------------------------------------------




------------------------------------------------------------------


-----------------------------------------------------------------------------






LEMMA EmptyInterval == 1..0 = {}
  OBVIOUS

LEMMA EmptyFinite == IsFiniteSet({})
<1> DEFINE f == [i \in 1..0 |-> i]
<1>1. IsBijection(f, 1..0, {})
  BY EmptyInterval DEF IsBijection
<1>2. 0 \in Nat
  OBVIOUS
<1> QED
  BY <1>1, <1>2 DEF IsFiniteSet

(***************************************************************************)
(* Restricting a bijection on 1..(n+1) to 1..n yields a bijection onto the *)
(* target set with the image of the last point removed.                    *)
(***************************************************************************)
LEMMA RestrictBijection ==
  ASSUME NEW n \in Nat, NEW f, NEW T, IsBijection(f, 1..(n+1), T)
  PROVE  IsBijection([i \in 1..n |-> f[i]], 1..n, T \ {f[n+1]})
<1> DEFINE g == [i \in 1..n |-> f[i]]
<1> DEFINE T1 == T \ {f[n+1]}
<1>0. /\ f \in [1..(n+1) -> T]
      /\ \A x, y \in 1..(n+1) : (x # y) => (f[x] # f[y])
      /\ \A y \in T : \E x \in 1..(n+1) : f[x] = y
  BY DEF IsBijection
<1>e. n+1 \in 1..(n+1)
  OBVIOUS
<1>a. \A i \in 1..n : i \in 1..(n+1) /\ i # n+1
  OBVIOUS
<1>1. g \in [1..n -> T1]
  <2>1. \A i \in 1..n : f[i] \in T1
    <3> TAKE i \in 1..n
    <3>1. i \in 1..(n+1) /\ i # n+1
      BY <1>a
    <3>2. f[i] \in T
      BY <1>0, <3>1
    <3>3. f[i] # f[n+1]
      BY <1>0, <1>e, <3>1
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>1
<1>2. \A x, y \in 1..n : (x # y) => (g[x] # g[y])
  <2> TAKE x, y \in 1..n
  <2>1. x \in 1..(n+1) /\ y \in 1..(n+1)
    BY <1>a
  <2> QED
    BY <1>0, <2>1
<1>3. \A y \in T1 : \E x \in 1..n : g[x] = y
  <2> TAKE y \in T1
  <2>1. y \in T /\ y # f[n+1]
    OBVIOUS
  <2>2. PICK k \in 1..(n+1) : f[k] = y
    BY <1>0, <2>1
  <2>3. k # n+1
    BY <2>1, <2>2
  <2>4. k \in 1..n
    BY <2>2, <2>3
  <2>5. g[k] = f[k]
    BY <2>4
  <2> QED
    BY <2>2, <2>4, <2>5
<1> QED
  BY <1>1, <1>2, <1>3 DEF IsBijection

(***************************************************************************)
(* Extending a bijection on 1..m to 1..(m+1) by mapping the new point to a *)
(* fresh element t yields a bijection onto the target set with t added.     *)
(***************************************************************************)
LEMMA ExtendBijection ==
  ASSUME NEW m \in Nat, NEW h, NEW S1, NEW t, t \notin S1,
         IsBijection(h, 1..m, S1)
  PROVE  IsBijection([i \in 1..(m+1) |-> IF i = m+1 THEN t ELSE h[i]],
                     1..(m+1), S1 \cup {t})
<1> DEFINE h2 == [i \in 1..(m+1) |-> IF i = m+1 THEN t ELSE h[i]]
<1> DEFINE U == S1 \cup {t}
<1>0. /\ h \in [1..m -> S1]
      /\ \A x, y \in 1..m : (x # y) => (h[x] # h[y])
      /\ \A y \in S1 : \E x \in 1..m : h[x] = y
  BY DEF IsBijection
<1>a. \A i \in 1..(m+1) : (i # m+1) => i \in 1..m
  OBVIOUS
<1>b. \A i \in 1..m : i # m+1 /\ i \in 1..(m+1)
  OBVIOUS
<1>1. h2 \in [1..(m+1) -> U]
  <2>1. \A i \in 1..(m+1) : (IF i = m+1 THEN t ELSE h[i]) \in U
    <3> TAKE i \in 1..(m+1)
    <3>1. CASE i = m+1
      BY <3>1
    <3>2. CASE i # m+1
      <4>1. i \in 1..m
        BY <1>a, <3>2
      <4>2. h[i] \in S1
        BY <1>0, <4>1
      <4> QED
        BY <3>2, <4>2
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1
<1>2. \A x, y \in 1..(m+1) : (x # y) => (h2[x] # h2[y])
  <2> TAKE x, y \in 1..(m+1)
  <2> HAVE x # y
  <2>1. h2[x] = IF x = m+1 THEN t ELSE h[x]
    OBVIOUS
  <2>2. h2[y] = IF y = m+1 THEN t ELSE h[y]
    OBVIOUS
  <2>3. CASE x = m+1
    <3>1. y \in 1..m
      BY <1>a, <2>3
    <3>2. h[y] \in S1
      BY <1>0, <3>1
    <3>3. h2[x] = t /\ h2[y] = h[y]
      BY <2>1, <2>2, <2>3, <3>1
    <3> QED
      BY <3>2, <3>3
  <2>4. CASE y = m+1
    <3>1. x \in 1..m
      BY <1>a, <2>4
    <3>2. h[x] \in S1
      BY <1>0, <3>1
    <3>3. h2[x] = h[x] /\ h2[y] = t
      BY <2>1, <2>2, <2>4, <3>1
    <3> QED
      BY <3>2, <3>3
  <2>5. CASE x # m+1 /\ y # m+1
    <3>1. x \in 1..m /\ y \in 1..m
      BY <1>a, <2>5
    <3>2. h[x] # h[y]
      BY <1>0, <3>1
    <3>3. h2[x] = h[x] /\ h2[y] = h[y]
      BY <2>1, <2>2, <2>5
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>3, <2>4, <2>5
<1>3. \A y \in U : \E x \in 1..(m+1) : h2[x] = y
  <2> TAKE y \in U
  <2>1. CASE y = t
    <3>1. m+1 \in 1..(m+1)
      OBVIOUS
    <3>2. h2[m+1] = t
      OBVIOUS
    <3> QED
      BY <2>1, <3>1, <3>2
  <2>2. CASE y # t
    <3>1. y \in S1
      BY <2>2
    <3>2. PICK k \in 1..m : h[k] = y
      BY <1>0, <3>1
    <3>3. k \in 1..(m+1) /\ k # m+1
      BY <1>b, <3>2
    <3>4. h2[k] = h[k]
      BY <3>3
    <3> QED
      BY <3>2, <3>3, <3>4
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEF IsBijection

(***************************************************************************)
(* Inductive statement: every subset of a set of size n is finite and has  *)
(* cardinality (via a bijection from some 1..m, m <= n) at most n.          *)
(***************************************************************************)
P(n) == \A T, S : (\E f : IsBijection(f, 1..n, T)) /\ (S \subseteq T)
                  => /\ IsFiniteSet(S)
                     /\ \E mm \in 0..n : \E g : IsBijection(g, 1..mm, S)

LEMMA Base == P(0)
<1> SUFFICES ASSUME NEW T, NEW S,
                    (\E f : IsBijection(f, 1..0, T)), S \subseteq T
             PROVE  /\ IsFiniteSet(S)
                    /\ \E mm \in 0..0 : \E g : IsBijection(g, 1..mm, S)
  BY DEF P
<1>1. PICK f : IsBijection(f, 1..0, T)
  OBVIOUS
<1>2. T = {}
  <2>1. \A y \in T : \E x \in 1..0 : f[x] = y
    BY <1>1 DEF IsBijection
  <2> QED
    BY <2>1, EmptyInterval
<1>3. S = {}
  BY <1>2
<1>4. IsFiniteSet(S)
  BY <1>3, EmptyFinite
<1>5. \E mm \in 0..0 : \E g : IsBijection(g, 1..mm, S)
  <2> DEFINE g0 == [i \in 1..0 |-> i]
  <2>1. IsBijection(g0, 1..0, {})
    BY EmptyInterval DEF IsBijection
  <2>2. IsBijection(g0, 1..0, S)
    BY <2>1, <1>3
  <2>3. 0 \in 0..0
    OBVIOUS
  <2> QED
    BY <2>2, <2>3
<1> QED
  BY <1>4, <1>5

LEMMA Step == \A n \in Nat : P(n) => P(n+1)
<1> SUFFICES ASSUME NEW n \in Nat, P(n)
             PROVE  P(n+1)
  OBVIOUS
<1> SUFFICES ASSUME NEW T, NEW S,
                    (\E f : IsBijection(f, 1..(n+1), T)), S \subseteq T
             PROVE  /\ IsFiniteSet(S)
                    /\ \E mm \in 0..(n+1) : \E g : IsBijection(g, 1..mm, S)
  BY DEF P
<1>1. PICK f : IsBijection(f, 1..(n+1), T)
  OBVIOUS
<1>2. n+1 \in 1..(n+1)
  OBVIOUS
<1>3. f[n+1] \in T
  BY <1>1, <1>2 DEF IsBijection
<1>4. IsBijection([i \in 1..n |-> f[i]], 1..n, T \ {f[n+1]})
  BY <1>1, RestrictBijection
<1>5. \E ff : IsBijection(ff, 1..n, T \ {f[n+1]})
  BY <1>4
<1>6. CASE f[n+1] \notin S
  <2>1. S \subseteq T \ {f[n+1]}
    BY <1>6
  <2>2. /\ IsFiniteSet(S)
        /\ \E mm \in 0..n : \E g : IsBijection(g, 1..mm, S)
    BY <1>5, <2>1 DEF P
  <2>3a. PICK mm \in 0..n : \E g : IsBijection(g, 1..mm, S)
    BY <2>2
  <2>3. PICK g : IsBijection(g, 1..mm, S)
    BY <2>3a
  <2>4. mm \in 0..(n+1)
    BY <2>3a
  <2>5. IsFiniteSet(S)
    BY <2>2
  <2> QED
    BY <2>3, <2>4, <2>5
<1>7. CASE f[n+1] \in S
  <2> DEFINE S1 == S \ {f[n+1]}
  <2>1. S1 \subseteq T \ {f[n+1]}
    OBVIOUS
  <2>2. /\ IsFiniteSet(S1)
        /\ \E mm \in 0..n : \E g : IsBijection(g, 1..mm, S1)
    BY <1>5, <2>1 DEF P
  <2>3a. PICK mm \in 0..n : \E g : IsBijection(g, 1..mm, S1)
    BY <2>2
  <2>3. PICK g : IsBijection(g, 1..mm, S1)
    BY <2>3a
  <2>4. mm \in Nat
    BY <2>3a
  <2>5. f[n+1] \notin S1
    OBVIOUS
  <2> DEFINE h2 == [i \in 1..(mm+1) |-> IF i = mm+1 THEN f[n+1] ELSE g[i]]
  <2>6. IsBijection(h2, 1..(mm+1), S1 \cup {f[n+1]})
    BY <2>3, <2>4, <2>5, ExtendBijection
  <2>7. S1 \cup {f[n+1]} = S
    BY <1>7
  <2>8. IsBijection(h2, 1..(mm+1), S)
    BY <2>6, <2>7
  <2>9. mm+1 \in Nat
    BY <2>4
  <2>10. IsFiniteSet(S)
    BY <2>8, <2>9 DEF IsFiniteSet
  <2>11. mm+1 \in 0..(n+1)
    BY <2>3a
  <2>12. \E mmm \in 0..(n+1) : \E gg : IsBijection(gg, 1..mmm, S)
    BY <2>8, <2>11
  <2> QED
    BY <2>10, <2>12
<1> QED
  BY <1>6, <1>7

LEMMA Pthm == \A n \in Nat : P(n)
<1>1. P(0)
  BY Base
<1>2. \A n \in Nat : P(n) => P(n+1)
  BY Step
<1> QED
  BY <1>1, <1>2, NatInduction

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
<1>1. Cardinality(TT) \in Nat
      /\ \E f : IsBijection(f, 1..Cardinality(TT), TT)
  <2>1. (Cardinality(TT) = Cardinality(TT))
          <=> (Cardinality(TT) \in Nat
               /\ \E f : IsBijection(f, 1..Cardinality(TT), TT))
    BY CardinalityAxiom
  <2> QED
    BY <2>1
<1>2. P(Cardinality(TT))
  BY <1>1, Pthm
<1>3. /\ IsFiniteSet(S)
      /\ \E mm \in 0..Cardinality(TT) : \E g : IsBijection(g, 1..mm, S)
  BY <1>1, <1>2 DEF P
<1>4. IsFiniteSet(S)
  BY <1>3
<1>5a. PICK mm \in 0..Cardinality(TT) : \E g : IsBijection(g, 1..mm, S)
  BY <1>3
<1>5. PICK g : IsBijection(g, 1..mm, S)
  BY <1>5a
<1>6. mm \in Nat
  BY <1>5a, <1>1
<1>7. mm = Cardinality(S)
  <2>1. (mm = Cardinality(S))
          <=> (mm \in Nat /\ \E ff : IsBijection(ff, 1..mm, S))
    BY <1>4, CardinalityAxiom
  <2>2. mm \in Nat /\ \E ff : IsBijection(ff, 1..mm, S)
    BY <1>5, <1>6
  <2> QED
    BY <2>1, <2>2
<1>8. mm \leq Cardinality(TT)
  BY <1>5a, <1>1
<1>9. Cardinality(S) \leq Cardinality(TT)
  BY <1>7, <1>8
<1> QED
  BY <1>4, <1>9
-------------------------------------------------------


-----------------------------------------------------------------------------

-------------------------------------------------------



=============================================================================
