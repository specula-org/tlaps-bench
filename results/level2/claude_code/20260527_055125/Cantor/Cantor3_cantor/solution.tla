

-------------- MODULE Cantor3_cantor ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1> TAKE S
  <1> TAKE f \in [S -> SUBSET S]
  <1> DEFINE D == {y \in S : y \notin f[y]}
  <1>1. D \in SUBSET S
    OBVIOUS
  <1>2. \A x \in S : f[x] # D
    <2> SUFFICES ASSUME NEW x \in S, f[x] = D
                 PROVE FALSE
      OBVIOUS
    <2> QED
      BY DEF D
  <1> QED
    BY <1>1, <1>2
===============================================
