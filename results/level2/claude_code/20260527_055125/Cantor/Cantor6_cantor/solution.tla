

-------------- MODULE Cantor6_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
<1> TAKE S, f
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>1. A \in SUBSET S
  OBVIOUS
<1>2. \A x \in S : f[x] # A
  <2> TAKE x \in S
  <2> SUFFICES ASSUME f[x] = A
               PROVE FALSE
    OBVIOUS
  <2>1. x \in A <=> x \notin f[x]
    BY DEF A
  <2> QED
    BY <2>1
<1> QED
  BY <1>1, <1>2
===============================================
