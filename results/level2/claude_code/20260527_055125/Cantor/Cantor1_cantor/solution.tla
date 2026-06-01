

-------------- MODULE Cantor1_cantor -----------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
<1> TAKE S
<1> TAKE f \in [S -> SUBSET S]
<1> DEFINE T == {z \in S : z \notin f[z]}
<1>1. T \in SUBSET S
  BY DEF T
<1>2. \A x \in S : f[x] # T
  <2> TAKE x \in S
  <2> SUFFICES ASSUME f[x] = T PROVE FALSE
    OBVIOUS
  <2> QED
    BY DEF T
<1> QED
  BY <1>1, <1>2
===============================================
