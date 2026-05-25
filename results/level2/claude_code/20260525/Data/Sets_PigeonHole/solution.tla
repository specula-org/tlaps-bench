-------------------------------- MODULE Sets_PigeonHole --------------------------------
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






-------------------------------------------------------


-----------------------------------------------------------------------------

(****************************************************************************)
(* Scaffolding for the proof of the pigeonhole principle.                   *)
(*                                                                          *)
(* Inj(g, m, n) asserts that g is an injection from the integer interval    *)
(* 1..m into the interval 1..n.                                             *)
(****************************************************************************)
Inj(g, m, n) == /\ g \in [1..m -> 1..n]
                /\ \A i, j \in 1..m : i # j => g[i] # g[j]

(****************************************************************************)
(* PHProp(n) is the core pigeonhole statement specialised to intervals:     *)
(* there is no injection from 1..m to 1..n when m > n.                      *)
(****************************************************************************)
PHProp(n) == \A m \in Nat : (\E g : Inj(g, m, n)) => m <= n

(****************************************************************************)
(* Consequences of the cardinality axiom for a finite set U: its           *)
(* cardinality is a natural number and there is a bijection from            *)
(* 1..Cardinality(U) to U.                                                  *)
(****************************************************************************)
LEMMA CardProps ==
  ASSUME NEW U, IsFiniteSet(U)
  PROVE  /\ Cardinality(U) \in Nat
         /\ \E ff : IsBijection(ff, 1 .. Cardinality(U), U)
<1>1. (Cardinality(U) = Cardinality(U))
         <=> ((Cardinality(U) \in Nat)
              /\ \E ff : IsBijection(ff, 1 .. Cardinality(U), U))
  BY CardinalityAxiom
<1> QED BY <1>1

(****************************************************************************)
(* The pigeonhole principle for integer intervals, proved by induction on  *)
(* n.  This is the combinatorial heart of the theorem.                     *)
(****************************************************************************)
LEMMA IntervalPigeonHole == \A n \in Nat : PHProp(n)
<1>1. PHProp(0)
  <2> SUFFICES ASSUME NEW m \in Nat, \E g : Inj(g, m, 0)
               PROVE  m <= 0
    BY DEF PHProp
  <2>1. PICK g : Inj(g, m, 0)
    OBVIOUS
  <2>2. g \in [1..m -> 1..0]
    BY <2>1 DEF Inj
  <2> SUFFICES ASSUME m # 0 PROVE FALSE
    OBVIOUS
  <2>3. 1 \in 1..m
    BY m \in Nat
  <2>4. g[1] \in 1..0
    BY <2>2, <2>3
  <2> QED
    BY <2>4
<1>2. ASSUME NEW n \in Nat, PHProp(n)
      PROVE  PHProp(n+1)
  <2>IH. PHProp(n)
    BY <1>2
  <2> SUFFICES ASSUME NEW m \in Nat, \E g : Inj(g, m, n+1)
               PROVE  m <= n+1
    BY DEF PHProp
  <2>1. PICK g : Inj(g, m, n+1)
    OBVIOUS
  <2>g. /\ g \in [1..m -> 1 .. (n+1)]
        /\ \A i, j \in 1..m : i # j => g[i] # g[j]
    BY <2>1 DEF Inj
  <2> SUFFICES ASSUME m # 0 PROVE m <= n+1
    BY n \in Nat
  <2>m1. m - 1 \in Nat
    BY m \in Nat
  <2>mm. m \in 1..m
    BY m \in Nat
  <2>hin. \A i \in 1 .. (m-1) : i \in 1..m
    BY m \in Nat
  <2> DEFINE h == [i \in 1 .. (m-1) |-> IF g[i] = n+1 THEN g[m] ELSE g[i]]
  <2>h1. \A i \in 1 .. (m-1) : h[i] = (IF g[i] = n+1 THEN g[m] ELSE g[i])
    BY DEF h
  <2>hval. \A i \in 1 .. (m-1) : h[i] \in 1..n
    <3> TAKE i \in 1 .. (m-1)
    <3>1. i \in 1..m
      BY <2>hin
    <3>2. g[i] \in 1 .. (n+1)
      BY <2>g, <3>1
    <3>3. h[i] = (IF g[i] = n+1 THEN g[m] ELSE g[i])
      BY <2>h1
    <3>4. CASE g[i] = n+1
      <4>1. h[i] = g[m]
        BY <3>3, <3>4
      <4>2. g[m] \in 1 .. (n+1)
        BY <2>g, <2>mm
      <4>3. i # m
        BY m \in Nat
      <4>4. g[i] # g[m]
        BY <2>g, <3>1, <2>mm, <4>3
      <4>5. g[m] # n+1
        BY <4>4, <3>4
      <4> QED
        BY <4>1, <4>2, <4>5, n \in Nat
    <3>5. CASE g[i] # n+1
      <4>1. h[i] = g[i]
        BY <3>3, <3>5
      <4> QED
        BY <4>1, <3>2, <3>5, n \in Nat
    <3> QED
      BY <3>4, <3>5
  <2>hfun. h \in [1 .. (m-1) -> 1..n]
    BY <2>hval DEF h
  <2>hinj. \A i, j \in 1 .. (m-1) : i # j => h[i] # h[j]
    <3> TAKE i, j \in 1 .. (m-1)
    <3> SUFFICES ASSUME i # j PROVE h[i] # h[j]
      OBVIOUS
    <3>i. i \in 1..m
      BY <2>hin
    <3>j. j \in 1..m
      BY <2>hin
    <3>hi. h[i] = (IF g[i] = n+1 THEN g[m] ELSE g[i])
      BY <2>h1
    <3>hj. h[j] = (IF g[j] = n+1 THEN g[m] ELSE g[j])
      BY <2>h1
    <3>gij. g[i] # g[j]
      BY <2>g, <3>i, <3>j
    <3>1. CASE g[i] = n+1 /\ g[j] = n+1
      BY <3>1, <3>gij
    <3>2. CASE g[i] = n+1 /\ g[j] # n+1
      <4>1. h[i] = g[m]
        BY <3>hi, <3>2
      <4>2. h[j] = g[j]
        BY <3>hj, <3>2
      <4>3. j # m
        BY m \in Nat
      <4>4. g[j] # g[m]
        BY <2>g, <3>j, <2>mm, <4>3
      <4> QED
        BY <4>1, <4>2, <4>4
    <3>3. CASE g[i] # n+1 /\ g[j] = n+1
      <4>1. h[i] = g[i]
        BY <3>hi, <3>3
      <4>2. h[j] = g[m]
        BY <3>hj, <3>3
      <4>3. i # m
        BY m \in Nat
      <4>4. g[i] # g[m]
        BY <2>g, <3>i, <2>mm, <4>3
      <4> QED
        BY <4>1, <4>2, <4>4
    <3>4. CASE g[i] # n+1 /\ g[j] # n+1
      <4>1. h[i] = g[i]
        BY <3>hi, <3>4
      <4>2. h[j] = g[j]
        BY <3>hj, <3>4
      <4> QED
        BY <4>1, <4>2, <3>gij
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2>hInj. Inj(h, m-1, n)
    BY <2>hfun, <2>hinj DEF Inj
  <2>ex. \E gg : Inj(gg, m-1, n)
    BY <2>hInj
  <2>ph. (m-1) <= n
    <3>1. \A mm \in Nat : (\E gg : Inj(gg, mm, n)) => mm <= n
      BY <2>IH DEF PHProp
    <3> QED
      BY <3>1, <2>ex, <2>m1
  <2> QED
    BY <2>ph, m \in Nat
<1> QED
  BY <1>1, <1>2, NatInduction

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
<1> SUFFICES ASSUME NEW S, NEW T,
                    IsFiniteSet(S), IsFiniteSet(T),
                    Cardinality(T) < Cardinality(S),
                    NEW f \in [S -> T]
             PROVE  \E x, y \in S : x # y /\ f[x] = f[y]
  OBVIOUS
<1> DEFINE p == Cardinality(S)
<1> DEFINE q == Cardinality(T)
<1>S. p \in Nat /\ \E bg : IsBijection(bg, 1..p, S)
  BY CardProps DEF p
<1>T. q \in Nat /\ \E bh : IsBijection(bh, 1..q, T)
  BY CardProps DEF q
<1> SUFFICES ASSUME \A x, y \in S : x # y => f[x] # f[y]
             PROVE  FALSE
  OBVIOUS
<1> PICK bg : IsBijection(bg, 1..p, S)
  BY <1>S
<1> PICK bh : IsBijection(bh, 1..q, T)
  BY <1>T
<1>bg. /\ bg \in [1..p -> S]
       /\ \A x, y \in 1..p : x # y => bg[x] # bg[y]
  BY DEF IsBijection
<1>bh. /\ bh \in [1..q -> T]
       /\ \A y \in T : \E x \in 1..q : bh[x] = y
  BY DEF IsBijection
<1> DEFINE c == [i \in 1..p |-> CHOOSE j \in 1..q : bh[j] = f[bg[i]]]
<1>cex. \A i \in 1..p : \E j \in 1..q : bh[j] = f[bg[i]]
  <2> TAKE i \in 1..p
  <2>1. bg[i] \in S
    BY <1>bg
  <2>2. f[bg[i]] \in T
    BY <2>1
  <2> QED
    BY <2>2, <1>bh
<1>cfun. c \in [1..p -> 1..q]
  <2>1. \A i \in 1..p : c[i] \in 1..q
    <3> TAKE i \in 1..p
    <3>1. c[i] = CHOOSE j \in 1..q : bh[j] = f[bg[i]]
      BY DEF c
    <3>2. \E j \in 1..q : bh[j] = f[bg[i]]
      BY <1>cex
    <3>3. (CHOOSE j \in 1..q : bh[j] = f[bg[i]]) \in 1..q
      BY <3>2
    <3> QED
      BY <3>1, <3>3
  <2> QED
    BY <2>1 DEF c
<1>capp. \A i \in 1..p : bh[c[i]] = f[bg[i]]
  <2> TAKE i \in 1..p
  <2>1. c[i] = CHOOSE j \in 1..q : bh[j] = f[bg[i]]
    BY DEF c
  <2>2. \E j \in 1..q : bh[j] = f[bg[i]]
    BY <1>cex
  <2> QED
    BY <2>1, <2>2
<1>cinj. \A i1, i2 \in 1..p : i1 # i2 => c[i1] # c[i2]
  <2> TAKE i1, i2 \in 1..p
  <2> SUFFICES ASSUME i1 # i2, c[i1] = c[i2] PROVE FALSE
    OBVIOUS
  <2>1. bh[c[i1]] = f[bg[i1]]
    BY <1>capp
  <2>2. bh[c[i2]] = f[bg[i2]]
    BY <1>capp
  <2>3. f[bg[i1]] = f[bg[i2]]
    BY <2>1, <2>2
  <2>4. bg[i1] # bg[i2]
    BY <1>bg
  <2>5. bg[i1] \in S /\ bg[i2] \in S
    BY <1>bg
  <2> QED
    BY <2>3, <2>4, <2>5
<1>cInj. Inj(c, p, q)
  BY <1>cfun, <1>cinj DEF Inj
<1>fin. \E gg : Inj(gg, p, q)
  BY <1>cInj
<1>ph. p <= q
  <2>1. PHProp(q)
    BY IntervalPigeonHole, <1>T
  <2> QED
    BY <2>1, <1>fin, <1>S DEF PHProp
<1> QED
  BY <1>ph, <1>S, <1>T DEF p, q
-------------------------------------------------------



=============================================================================
