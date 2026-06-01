

-------------- MODULE Cantor2_cantor ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
<1> TAKE S
<1> TAKE f \in [S -> SUBSET S]
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>1. A \in SUBSET S
  OBVIOUS
<1>2. \A x \in S : f[x] # A
  <2> TAKE x \in S
  <2>1. SUFFICES ASSUME f[x] = A
                 PROVE FALSE
    OBVIOUS
  <2>2. x \in A <=> x \notin f[x]
    OBVIOUS
  <2>3. QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2
===============================================
