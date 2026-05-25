(* Contributed by Leslie Lamport *)

-------------- MODULE Cantor3_cantor ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. TAKE S
  <1>2. TAKE f \in [S -> SUBSET S]
  <1> DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    OBVIOUS
  <1>4. \A x \in S : f[x] # A
    <2>1. TAKE x \in S
    <2>2. CASE x \in A
      <3>1. x \notin f[x]
        BY <2>2
      <3> QED
        BY <2>2, <3>1
    <2>3. CASE x \notin A
      <3>1. x \in f[x]
        BY <2>3
      <3> QED
        BY <2>3, <3>1
    <2> QED
      BY <2>2, <2>3
  <1> QED
    BY <1>3, <1>4
===============================================
