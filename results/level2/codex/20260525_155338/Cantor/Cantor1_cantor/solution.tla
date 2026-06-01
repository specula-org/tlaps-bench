

-------------- MODULE Cantor1_cantor -----------------
Diagonal(S, f) == {x \in S : x \notin f[x]}

THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
<1>1. SUFFICES ASSUME NEW S,
                      NEW f \in [S -> SUBSET S]
              PROVE  \E A \in SUBSET S :
                       \A x \in S :
                         f[x] # A
  OBVIOUS
<1>2. Diagonal(S, f) \in SUBSET S
  BY DEF Diagonal
<1>3. \A x \in S : f[x] # Diagonal(S, f)
  BY <1>1 DEF Diagonal
<1>4. QED
  BY <1>2, <1>3
===============================================
